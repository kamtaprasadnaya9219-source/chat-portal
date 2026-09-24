"""
Chat Portal (app-5)
===================
Accounts (username + password), public chat, groups, private groups,
direct messages, per-user themes, and admin/owner password recovery.

Run:
    pip install flask
    OWNER_PASSWORD=... ADMIN_PASSWORD=... python app-5.py

Data is saved in chat_data.json (next to this file). Keep that file private:
it contains password hashes. Override the location with DATA_FILE=/path.
"""

import hashlib
import json
import os
import re
import secrets
import threading
import time
import uuid
from datetime import datetime
from functools import wraps

from flask import (
    Flask, abort, jsonify, redirect, render_template_string,
    request, session, url_for
)
from werkzeug.security import check_password_hash, generate_password_hash

# =========================================================
# CONFIG
# =========================================================

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_FILE = os.environ.get("DATA_FILE", os.path.join(BASE_DIR, "chat_data.json"))
SECRET_FILE = os.path.join(BASE_DIR, ".secret_key")

def env_password(name, default):
    """Returns (password, source). Spaces and stray quotes around the
    value are removed (Windows `set NAME="abc"` keeps the quotes)."""
    raw = os.environ.get(name)
    value = (raw or "").strip().strip("\"'").strip()

    if value:
        return value, "environment variable"

    return default, "DEFAULT"


def required_password(name):
    raw = os.environ.get(name)
    value = (raw or "").strip().strip("\"'").strip()

    if not value:
        raise RuntimeError(f"{name} is not set. Set it as an environment variable.")

    if len(value) < 10:
        raise RuntimeError(f"{name} must be at least 10 characters long.")

    return value, "environment variable"


OWNER_PASSWORD, OWNER_SOURCE = required_password("OWNER_PASSWORD")
ADMIN_PASSWORD, ADMIN_SOURCE = required_password("ADMIN_PASSWORD")

ONLINE_WINDOW = 45              # seconds without polling => offline
STAFF_TIMEOUT = 600             # admin/owner session idle timeout

MIN_USERNAME_LENGTH = 3
MAX_USERNAME_LENGTH = 30
MIN_PASSWORD_LENGTH = 6
MAX_PASSWORD_LENGTH = 128
MAX_MESSAGE_LENGTH = 500
MAX_STORED_PER_ROOM = 300       # older messages are dropped
MAX_ROOM_NAME_LENGTH = 40
MAX_ROOMS_PER_USER = 20
MAX_GROUP_MEMBERS = 200
TEMP_PASSWORD_HOURS = 24

LOGIN_MAX_ATTEMPTS = 5
LOGIN_WINDOW_SECONDS = 300
LOGIN_LOCKOUT_SECONDS = 300

RESERVED_NAMES = {"admin", "owner", "administrator", "system", "moderator"}
THEME_PRESETS = {"slate", "midnight", "amoled", "light", "mint",
                 "lavender", "peach", "sky", "rose"}
DEFAULT_THEME = {"preset": "slate", "accent": "#2563eb"}
HEX_COLOR = re.compile(r"^#[0-9a-fA-F]{6}$")


def load_secret_key():
    """Env var first, then a saved key file, so login sessions
    survive a restart."""
    env_key = os.environ.get("FLASK_SECRET_KEY")

    if env_key:
        return env_key

    try:
        with open(SECRET_FILE, encoding="utf-8") as f:
            saved = f.read().strip()

        if saved:
            return saved
    except OSError:
        pass

    key = secrets.token_hex(32)

    try:
        fd = os.open(SECRET_FILE, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)

        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(key)
    except OSError:
        pass

    return key


app = Flask(__name__)
app.secret_key = load_secret_key()
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    PERMANENT_SESSION_LIFETIME=60 * 60 * 24 * 30,
)


@app.after_request
def security_headers(response):
    response.headers.setdefault("X-Content-Type-Options", "nosniff")
    response.headers.setdefault("X-Frame-Options", "DENY")
    response.headers.setdefault("Referrer-Policy", "same-origin")

    if request.path.startswith("/api/"):
        response.headers["Cache-Control"] = "no-store"

    return response


# =========================================================
# STORAGE (JSON file, saved on every change)
# =========================================================
#
# users    : { ukey: {username, pw_hash, created, pw_ver, must_change,
#                     temp_until, theme:{preset, accent}} }
# rooms    : { room_id: {id, type, name, owner, members[ukeys], created,
#                        updated, seq} }
#            type = public | group | private_group | dm
# messages : { room_id: [ {id, k, u, t, ts} ] }
# recovery : [ {id, guess, note, ts, done} ]
#
# ukey = username.casefold()  (usernames are unique ignoring case)

LOCK = threading.RLock()


def now():
    return time.time()


def new_public_room():
    return {
        "id": "public", "type": "public", "name": "Public Chat",
        "owner": None, "members": [], "created": now(),
        "updated": now(), "seq": 0
    }


def load_db():
    data = {}

    try:
        with open(DATA_FILE, encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        data = {}
    except (OSError, ValueError):
        # Unreadable file: keep a copy instead of overwriting it.
        try:
            os.replace(DATA_FILE, f"{DATA_FILE}.corrupt-{int(now())}")
        except OSError:
            pass
        data = {}

    db = {
        "users": data.get("users", {}),
        "rooms": data.get("rooms", {}),
        "messages": data.get("messages", {}),
        "recovery": data.get("recovery", []),
    }

    if "public" not in db["rooms"]:
        db["rooms"]["public"] = new_public_room()

    db["messages"].setdefault("public", [])
    return db


def save_db():
    """Atomic write: temp file, then replace. Call while holding LOCK."""
    tmp = DATA_FILE + ".tmp"

    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(DB, f, ensure_ascii=False)

    try:
        os.chmod(tmp, 0o600)
    except OSError:
        pass

    os.replace(tmp, DATA_FILE)


DB = load_db()

# ---- temporary (memory-only) state; fine to lose on restart ----
PRESENCE = {}          # ukey -> last poll time
admin_sessions = {}    # staff sessions (admin / owner)
login_attempts = {}    # ip -> brute-force counters
THROTTLES = {}         # (bucket, key) -> [timestamps]

# Hash used to spend the same time when a username doesn't exist.
DUMMY_HASH = generate_password_hash("not-a-real-password")


# =========================================================
# HELPERS
# =========================================================

def ukey(name):
    return str(name).strip().casefold()


def fmt_time(ts):
    return datetime.fromtimestamp(ts).strftime("%d %b %Y, %H:%M")


def fmt_clock(ts):
    return datetime.fromtimestamp(ts).strftime("%H:%M:%S")


def get_client_ip():
    return request.remote_addr or "unknown"


def throttle_hit(bucket, key, limit, window):
    """Record a hit. Returns False when the limit is already reached."""
    k = (bucket, key)
    current = now()
    hits = [t for t in THROTTLES.get(k, []) if current - t < window]

    if len(hits) >= limit:
        THROTTLES[k] = hits
        return False

    hits.append(current)
    THROTTLES[k] = hits
    return True


def cleanup():
    """Drop stale presence, expired staff sessions and old counters."""
    current = now()

    for k in [k for k, t in PRESENCE.items() if current - t > ONLINE_WINDOW * 4]:
        PRESENCE.pop(k, None)

    for sid in [s for s, d in admin_sessions.items()
                if current - d["last_seen"] > STAFF_TIMEOUT]:
        admin_sessions.pop(sid, None)

    for ip in list(login_attempts):
        data = login_attempts[ip]

        if data["locked_until"]:
            if current > data["locked_until"] + LOGIN_WINDOW_SECONDS:
                login_attempts.pop(ip, None)
        elif current - data["first_attempt"] > LOGIN_WINDOW_SECONDS:
            login_attempts.pop(ip, None)

    for k in list(THROTTLES):
        THROTTLES[k] = [t for t in THROTTLES[k] if current - t < 3600]

        if not THROTTLES[k]:
            THROTTLES.pop(k, None)


def is_online(k):
    t = PRESENCE.get(k)
    return bool(t) and now() - t < ONLINE_WINDOW


def display_name(k):
    user = DB["users"].get(k)
    return user["username"] if user else "Deleted user"


# ---------------------------------------------------------
# Validation
# ---------------------------------------------------------

def check_username(raw):
    """Returns (clean_name, error)."""
    name = (raw or "").strip()

    if len(name) < MIN_USERNAME_LENGTH:
        return None, f"Username must be at least {MIN_USERNAME_LENGTH} characters."

    if len(name) > MAX_USERNAME_LENGTH:
        return None, f"Username must be {MAX_USERNAME_LENGTH} characters or less."

    if not name.isprintable():
        return None, "Username contains invalid characters."

    if ukey(name) in RESERVED_NAMES:
        return None, "This username is reserved."

    if ukey(name) in DB["users"]:
        return None, "This username is already taken."

    return name, None


def check_password(pw):
    if len(pw) < MIN_PASSWORD_LENGTH:
        return f"Password must be at least {MIN_PASSWORD_LENGTH} characters."

    if len(pw) > MAX_PASSWORD_LENGTH:
        return f"Password must be {MAX_PASSWORD_LENGTH} characters or less."

    return None


def safe_equal(a, b):
    return secrets.compare_digest(str(a).encode(), str(b).encode())


# ---------------------------------------------------------
# CSRF
# ---------------------------------------------------------

def get_csrf_token():
    token = session.get("csrf_token")

    if not token:
        token = secrets.token_hex(16)
        session["csrf_token"] = token

    return token


def csrf_valid():
    submitted = request.form.get("csrf_token") or request.headers.get("X-CSRF-Token", "")
    real = session.get("csrf_token", "")

    if not real:
        return False

    return safe_equal(submitted, real)


# ---------------------------------------------------------
# Login brute-force protection (per IP)
# ---------------------------------------------------------

def is_locked_out(ip):
    data = login_attempts.get(ip)

    if not data or not data["locked_until"]:
        return False

    return now() < data["locked_until"]


def lockout_remaining(ip):
    data = login_attempts.get(ip)

    if not data or not data["locked_until"]:
        return 0

    return max(0, int(data["locked_until"] - now()))


def register_failed_login(ip):
    current = now()
    data = login_attempts.get(ip)

    if not data or current - data["first_attempt"] > LOGIN_WINDOW_SECONDS:
        data = {"count": 0, "first_attempt": current, "locked_until": None}

    data["count"] += 1

    if data["count"] >= LOGIN_MAX_ATTEMPTS:
        data["locked_until"] = current + LOGIN_LOCKOUT_SECONDS

    login_attempts[ip] = data


def register_successful_login(ip):
    login_attempts.pop(ip, None)


# ---------------------------------------------------------
# Current user (session -> account)
# ---------------------------------------------------------

def current_user():
    """Logged-in account or None. Sessions die when the password
    changes/resets or an admin kicks the user (pw_ver changes)."""
    k = session.get("uk")

    if not k:
        return None

    user = DB["users"].get(k)

    if not user or session.get("pv") != user["pw_ver"]:
        session.pop("uk", None)
        session.pop("pv", None)
        return None

    return user


def login_session(k):
    user = DB["users"][k]
    session.permanent = True
    session["uk"] = k
    session["pv"] = user["pw_ver"]
    # Fresh CSRF token for the new login (staff session, if any, is kept).
    session["csrf_token"] = secrets.token_hex(16)


def api(fn):
    """JSON API guard: login, forced password change, CSRF, presence."""
    @wraps(fn)
    def wrapper(*args, **kwargs):
        with LOCK:
            user = current_user()

            if not user:
                return jsonify(error="login"), 401

            if user.get("must_change"):
                return jsonify(error="must_change"), 403

            if request.method == "POST" and not csrf_valid():
                return jsonify(error="Session expired. Please refresh the page."), 400

            PRESENCE[ukey(user["username"])] = now()
            return fn(user, *args, **kwargs)

    return wrapper


def body():
    data = request.get_json(silent=True)
    return data if isinstance(data, dict) else {}


# ---------------------------------------------------------
# Rooms
# ---------------------------------------------------------

def dm_room_id(a, b):
    joined = "\n".join(sorted([a, b]))
    return "dm_" + hashlib.sha256(joined.encode("utf-8")).hexdigest()[:16]


def can_read(room, k):
    if room["type"] == "public":
        return True

    return k in room["members"]


def room_view(room, k):
    t = room["type"]
    joined = t == "public" or k in room["members"]

    view = {
        "id": room["id"],
        "type": t,
        "joined": joined,
        "last_seq": room["seq"],
        "updated": room.get("updated", 0),
        "count": None if t == "public" else len(room["members"]),
        "is_owner": room.get("owner") == k,
    }

    if t == "dm":
        others = [m for m in room["members"] if m != k]
        view["name"] = display_name(others[0]) if others else "Deleted user"
    else:
        view["name"] = room["name"]

    return view


def visible_rooms(k):
    result = []

    for room in DB["rooms"].values():
        t = room["type"]

        if t == "public" or k in room["members"] or t == "group":
            result.append(room_view(room, k))

    return result


def delete_room(rid):
    if rid == "public":
        return

    DB["rooms"].pop(rid, None)
    DB["messages"].pop(rid, None)


def delete_account(k):
    """Remove an account and clean up rooms it belonged to."""
    DB["users"].pop(k, None)
    PRESENCE.pop(k, None)

    for rid, room in list(DB["rooms"].items()):
        if room["type"] == "public" or k not in room["members"]:
            continue

        room["members"].remove(k)

        if room["type"] == "dm" or not room["members"]:
            delete_room(rid)
        elif room.get("owner") == k:
            room["owner"] = room["members"][0]

    for req in DB["recovery"]:
        if ukey(req.get("guess", "")) == k:
            req["done"] = True


# =========================================================
# SHARED CSS + THEME JS (injected into every page)
# =========================================================

BASE_CSS = r"""
:root {
    --bg: #0f172a;
    --panel: #131d33;
    --card: #1e293b;
    --text: #f1f5f9;
    --muted: #94a3b8;
    --border: #334155;
    --bubble: #273449;
    --accent: #2563eb;
    --on-accent: #ffffff;
    --accent-soft: color-mix(in srgb, var(--accent) 16%, transparent);
    --danger: #ef4444;
    --ok: #22c55e;
}

* { box-sizing: border-box; }

html, body { height: 100%; }

body {
    margin: 0;
    background: var(--bg);
    color: var(--text);
    font-family: system-ui, -apple-system, "Segoe UI", Roboto, "Noto Sans", Arial, sans-serif;
    font-size: 15px;
    line-height: 1.45;
}

a { color: var(--accent); font-weight: 600; text-decoration: none; }
a:hover { text-decoration: underline; }

h1, h2, h3 { line-height: 1.2; }

input, textarea, select {
    width: 100%;
    padding: 11px 12px;
    border-radius: 10px;
    border: 1px solid var(--border);
    background: var(--bg);
    color: var(--text);
    font: inherit;
}

input[type="checkbox"], input[type="color"] { width: auto; padding: 0; }

input:focus-visible, textarea:focus-visible, select:focus-visible,
button:focus-visible, a:focus-visible {
    outline: 2px solid var(--accent);
    outline-offset: 2px;
}

.btn {
    display: inline-block;
    padding: 10px 16px;
    border: 0;
    border-radius: 10px;
    background: var(--accent);
    color: var(--on-accent);
    font: inherit;
    font-weight: 600;
    cursor: pointer;
}

.btn:hover { filter: brightness(1.08); }
.btn:active { transform: scale(.98); }
.btn.block { width: 100%; margin-top: 12px; }
.btn.danger { background: var(--danger); color: #fff; }
.btn.ghost { background: var(--card); color: var(--text); border: 1px solid var(--border); }
.btn.small { padding: 6px 10px; font-size: 13px; border-radius: 8px; }

.muted { color: var(--muted); }
.err { color: var(--danger); font-weight: 600; }
.okmsg { color: var(--ok); font-weight: 600; }

@media (prefers-reduced-motion: reduce) {
    * { transition: none !important; animation: none !important; }
}
"""


THEME_JS = r"""
const THEMES = {
    slate:    {name: "Slate",    dark: true,  bg: "#0f172a", panel: "#131d33", card: "#1e293b", text: "#f1f5f9", muted: "#94a3b8", border: "#334155", bubble: "#273449"},
    midnight: {name: "Midnight", dark: true,  bg: "#0a0f1f", panel: "#0f1730", card: "#162042", text: "#e6ebfa", muted: "#8792b5", border: "#24305c", bubble: "#1c2851"},
    amoled:   {name: "Black",    dark: true,  bg: "#000000", panel: "#0a0a0a", card: "#141414", text: "#f5f5f5", muted: "#8a8a8a", border: "#262626", bubble: "#1a1a1a"},
    light:    {name: "Light",    dark: false, bg: "#f3f5f9", panel: "#ffffff", card: "#ffffff", text: "#1b2333", muted: "#66718a", border: "#dfe4ee", bubble: "#e6ebf4"},
    mint:     {name: "Mint",     dark: false, bg: "#ecf8f2", panel: "#f7fdfa", card: "#ffffff", text: "#183328", muted: "#5d7b6c", border: "#cfe8db", bubble: "#d9efe3"},
    lavender: {name: "Lavender", dark: false, bg: "#f1eefb", panel: "#faf8ff", card: "#ffffff", text: "#251f3d", muted: "#70688f", border: "#dcd5f2", bubble: "#e5dff7"},
    peach:    {name: "Peach",    dark: false, bg: "#fff1e8", panel: "#fff9f5", card: "#ffffff", text: "#3a2519", muted: "#8a6b58", border: "#f3d9c8", bubble: "#fbe3d3"},
    sky:      {name: "Sky",      dark: false, bg: "#e8f4fd", panel: "#f5fbff", card: "#ffffff", text: "#152a3d", muted: "#59748c", border: "#cbe3f5", bubble: "#d6eafa"},
    rose:     {name: "Rose",     dark: false, bg: "#fdeef2", panel: "#fff8fa", card: "#ffffff", text: "#3d1d27", muted: "#8c5f6c", border: "#f5d3dc", bubble: "#f9dbe4"}
};

function onAccent(hex) {
    const n = parseInt(hex.slice(1), 16);
    const lum = (0.299 * (n >> 16 & 255) + 0.587 * (n >> 8 & 255) + 0.114 * (n & 255)) / 255;
    return lum > 0.62 ? "#111827" : "#ffffff";
}

function applyTheme(preset, accent) {
    const t = THEMES[preset] || THEMES.slate;
    const root = document.documentElement;
    const s = root.style;

    ["bg", "panel", "card", "text", "muted", "border", "bubble"].forEach(function(k) {
        s.setProperty("--" + k, t[k]);
    });

    s.setProperty("--accent", accent);
    s.setProperty("--on-accent", onAccent(accent));
    root.style.colorScheme = t.dark ? "dark" : "light";
}

(function() {
    try {
        const saved = JSON.parse(localStorage.getItem("chat_theme") || "null");

        if (saved && saved.preset && /^#[0-9a-fA-F]{6}$/.test(saved.accent || "")) {
            applyTheme(saved.preset, saved.accent);
        }
    } catch (e) {}
})();
"""


# =========================================================
# AUTH PAGES (login / register / forgot / change password
# and the admin/owner password screen)
# =========================================================

AUTH_HTML = r"""
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{{ title }}</title>
<style>
{{ base_css|safe }}

.wrap {
    min-height: 100%;
    display: grid;
    place-items: center;
    padding: 24px 16px;
}

.card {
    width: 100%;
    max-width: 400px;
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 18px;
    padding: 26px 24px;
}

.card h1 { margin: 0 0 4px; font-size: 24px; }
.card .sub { margin: 0 0 14px; color: var(--muted); }
.card label { display: block; margin-top: 12px; font-weight: 600; font-size: 14px; }
.card label input, .card label textarea { margin-top: 5px; font-weight: 400; }
.hint { font-size: 13px; color: var(--muted); margin: 5px 0 0; font-weight: 400; }
.links { margin-top: 16px; display: flex; justify-content: space-between; gap: 10px; flex-wrap: wrap; font-size: 14px; }
</style>
<script>{{ theme_js|safe }}</script>
</head>
<body>
<div class="wrap">
<div class="card">

<h1>{{ title }}</h1>
{% if subtitle %}<p class="sub">{{ subtitle }}</p>{% endif %}

{% if error %}<p class="err">{{ error }}</p>{% endif %}
{% if ok %}<p class="okmsg">{{ ok }}</p>{% endif %}

{% if mode != 'sent' %}
<form method="POST" action="{{ action }}">
<input type="hidden" name="csrf_token" value="{{ csrf_token }}">

{% if mode == 'login' %}
    <label>Username
        <input type="text" name="username" value="{{ values.username or '' }}" maxlength="30" autocomplete="username" required autofocus>
    </label>
    <label>Password
        <input type="password" name="password" autocomplete="current-password" required>
    </label>
    <button class="btn block" type="submit">Log in</button>
    <div class="links">
        <a href="{{ url_for('register') }}">Create account</a>
        <a href="{{ url_for('forgot') }}">Forgot username / password?</a>
    </div>

{% elif mode == 'register' %}
    <label>Username
        <input type="text" name="username" value="{{ values.username or '' }}" minlength="3" maxlength="30" autocomplete="username" required autofocus>
        <p class="hint">Choose carefully. Your username is set once and can't be changed later.</p>
    </label>
    <label>Password
        <input type="password" name="password" minlength="6" maxlength="128" autocomplete="new-password" required>
    </label>
    <label>Confirm password
        <input type="password" name="confirm" minlength="6" maxlength="128" autocomplete="new-password" required>
    </label>
    <button class="btn block" type="submit">Create account</button>
    <div class="links"><a href="{{ url_for('login') }}">I already have an account</a></div>

{% elif mode == 'forgot' %}
    <label>Username you remember (optional)
        <input type="text" name="username" value="{{ values.username or '' }}" maxlength="30" autocomplete="off">
    </label>
    <label>Anything that helps the admin find you (optional)
        <textarea name="note" rows="3" maxlength="200" placeholder="e.g. I joined yesterday, my name starts with R">{{ values.note or '' }}</textarea>
    </label>
    <button class="btn block" type="submit">Send request</button>
    <div class="links"><a href="{{ url_for('login') }}">Back to login</a></div>

{% elif mode == 'change' %}
    {% if not forced %}
    <label>Current password
        <input type="password" name="current" autocomplete="current-password" required autofocus>
    </label>
    {% endif %}
    <label>New password
        <input type="password" name="password" minlength="6" maxlength="128" autocomplete="new-password" required {% if forced %}autofocus{% endif %}>
    </label>
    <label>Confirm new password
        <input type="password" name="confirm" minlength="6" maxlength="128" autocomplete="new-password" required>
    </label>
    <button class="btn block" type="submit">Save password</button>
    {% if not forced %}<div class="links"><a href="{{ url_for('index') }}">Cancel</a></div>{% endif %}

{% elif mode == 'staff' %}
    <label>Password
        <input type="password" name="password" autocomplete="new-password" required autofocus>
    </label>
    <button class="btn block" type="submit">Login</button>
{% endif %}

</form>
{% else %}
    <div class="links"><a href="{{ url_for('login') }}">Back to login</a></div>
{% endif %}

</div>
</div>
</body>
</html>
"""


# =========================================================
# CHAT PAGE (single page app)
# =========================================================

CHAT_HTML = r"""
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>Chat</title>
<style>
{{ base_css|safe }}

body { overflow: hidden; }

#app { display: flex; height: 100vh; height: 100dvh; }

/* ---------- sidebar ---------- */
#sidebar {
    width: 310px;
    flex-shrink: 0;
    display: flex;
    flex-direction: column;
    min-height: 0;
    background: var(--panel);
    border-right: 1px solid var(--border);
}

.side-top { display: flex; align-items: center; gap: 10px; padding: 14px 14px 10px; }
.side-top .who { flex: 1; min-width: 0; }
.side-top .who b { display: block; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.side-top .who span { font-size: 12px; color: var(--muted); }

.side-actions { display: flex; gap: 6px; padding: 0 14px 10px; }
.side-actions .btn { flex: 1; padding: 8px 6px; font-size: 13px; }

#roomlist { flex: 1; overflow-y: auto; padding: 0 8px 16px; }

.sec { margin: 14px 8px 4px; font-size: 13px; font-weight: 700; color: var(--muted); }

.room {
    display: flex; align-items: center; gap: 10px;
    width: 100%; padding: 8px 10px;
    border: 0; border-radius: 10px;
    background: none; color: inherit;
    font: inherit; text-align: left; cursor: pointer;
}
.room:hover { background: var(--card); }
.room.active { background: var(--accent-soft); }
.room .nm { flex: 1; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.room .meta { font-size: 12px; color: var(--muted); }
.unread { width: 9px; height: 9px; border-radius: 50%; background: var(--accent); flex-shrink: 0; }

.av {
    position: relative; flex-shrink: 0;
    width: 34px; height: 34px; border-radius: 50%;
    display: grid; place-items: center;
    font-weight: 700; font-size: 14px; color: #fff;
}
.av.icon { background: var(--card); color: var(--text); font-size: 16px; border: 1px solid var(--border); }
.av .on {
    position: absolute; right: -2px; bottom: -2px;
    width: 11px; height: 11px; border-radius: 50%;
    background: var(--ok); border: 2px solid var(--panel);
}

/* ---------- chat pane ---------- */
#chat { flex: 1; min-width: 0; display: flex; flex-direction: column; }

#chead {
    display: flex; align-items: center; gap: 10px;
    padding: 10px 14px; background: var(--panel);
    border-bottom: 1px solid var(--border);
}
#chead .titles { flex: 1; min-width: 0; }
#rtitle { font-weight: 700; font-size: 17px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
#rsub { font-size: 12px; color: var(--muted); }
#menuBtn { display: none; }

.icon-btn {
    border: 1px solid var(--border); background: var(--card); color: var(--text);
    border-radius: 10px; padding: 7px 11px; font: inherit; font-size: 14px; cursor: pointer;
}
.icon-btn:hover { border-color: var(--accent); }

#msgs {
    flex: 1; overflow-y: auto; padding: 14px;
    display: flex; flex-direction: column;
}
.empty { margin: auto; color: var(--muted); text-align: center; }

.msg { display: flex; flex-direction: column; align-items: flex-start; max-width: 78%; margin: 5px 0; }
.msg.mine { align-self: flex-end; align-items: flex-end; }
.msg .who { font-size: 12px; font-weight: 600; color: var(--muted); margin: 0 6px 2px; }
.bubble {
    background: var(--bubble); padding: 8px 12px; border-radius: 16px 16px 16px 4px;
    white-space: pre-wrap; overflow-wrap: anywhere;
}
.msg.mine .bubble { background: var(--accent); color: var(--on-accent); border-radius: 16px 16px 4px 16px; }
.msg .ts { font-size: 11px; color: var(--muted); margin: 2px 6px 0; }

#composer {
    display: flex; gap: 8px; align-items: flex-end;
    padding: 10px 12px calc(10px + env(safe-area-inset-bottom));
    background: var(--panel); border-top: 1px solid var(--border);
}
#mtext { resize: none; max-height: 120px; min-height: 42px; }
#composer .btn { height: 42px; }

/* ---------- modal ---------- */
.scrim {
    position: fixed; inset: 0; z-index: 50;
    display: grid; place-items: center; padding: 16px;
    background: rgba(0, 0, 0, .5);
}
.modal {
    width: min(460px, 100%); max-height: 88vh;
    display: flex; flex-direction: column;
    background: var(--card); border: 1px solid var(--border); border-radius: 16px;
}
.mhead { display: flex; justify-content: space-between; align-items: center; padding: 14px 18px 6px; }
.mhead h2 { margin: 0; font-size: 18px; }
.mbody { padding: 6px 18px 18px; overflow-y: auto; }
.mbody p { margin: 6px 0 10px; }
.lbl { margin: 14px 0 6px; font-weight: 700; font-size: 14px; }

.ulist { margin-top: 8px; max-height: 240px; overflow-y: auto; border: 1px solid var(--border); border-radius: 10px; }
.urow {
    display: flex; align-items: center; gap: 10px; width: 100%;
    padding: 7px 10px; border: 0; background: none; color: inherit; font: inherit; text-align: left; cursor: pointer;
}
.urow:hover { background: var(--accent-soft); }
.urow .nm { flex: 1; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.urow .av .on { border-color: var(--card); }
.pad { padding: 12px; }

.themes { display: grid; grid-template-columns: repeat(3, 1fr); gap: 8px; }
.tchip {
    padding: 0; border: 2px solid var(--border); border-radius: 12px;
    background: none; color: var(--text); font: inherit; font-size: 13px; cursor: pointer; overflow: hidden;
}
.tchip .sw { height: 34px; display: flex; }
.tchip .sw i { flex: 1; }
.tchip span { display: block; padding: 5px 0; background: var(--card); }
.tchip.active { border-color: var(--accent); }

.accents { display: flex; flex-wrap: wrap; gap: 8px; align-items: center; }
.acc {
    width: 30px; height: 30px; padding: 0; border-radius: 50%;
    border: 3px solid transparent; cursor: pointer;
}
.acc.active { border-color: var(--text); }
input[type="color"].custom { width: 34px; height: 34px; border: 0; background: none; cursor: pointer; }

#toast {
    position: fixed; left: 50%; bottom: 84px; transform: translateX(-50%);
    z-index: 60; max-width: 90vw;
    background: var(--text); color: var(--bg);
    padding: 9px 14px; border-radius: 10px; font-weight: 600; font-size: 14px;
}

#sscrim { display: none; }

@media (max-width: 800px) {
    #sidebar {
        position: fixed; top: 0; bottom: 0; left: 0; z-index: 30;
        width: min(86vw, 330px);
        transform: translateX(-102%); transition: transform .2s ease;
    }
    #sidebar.open { transform: none; }
    #sidebar.open ~ #sscrim { display: block; position: fixed; inset: 0; z-index: 25; background: rgba(0, 0, 0, .45); }
    #menuBtn { display: inline-block; }
    .msg { max-width: 88%; }
}
</style>
<script>{{ theme_js|safe }}</script>
</head>
<body>

<script id="boot" type="application/json">{{ boot|tojson }}</script>

<div id="app">

    <aside id="sidebar">
        <div class="side-top">
            <div id="meAv"></div>
            <div class="who"><b id="meName"></b><span>Signed in</span></div>
            <button class="icon-btn" id="settingsBtn" type="button">Settings</button>
        </div>

        <div class="side-actions">
            <button class="btn" id="newDm" type="button">New DM</button>
            <button class="btn ghost" id="newGroup" type="button">+ Group</button>
            <button class="btn ghost" id="newPrivate" type="button">+ Private</button>
        </div>

        <nav id="roomlist" aria-label="Chats"></nav>
    </aside>

    <div id="sscrim"></div>

    <main id="chat">
        <header id="chead">
            <button class="icon-btn" id="menuBtn" type="button" aria-label="Show chats">Chats</button>
            <div class="titles">
                <div id="rtitle"></div>
                <div id="rsub"></div>
            </div>
            <button class="icon-btn" id="infoBtn" type="button" hidden>Members</button>
        </header>

        <div id="msgs" aria-live="polite"></div>

        <form id="composer" autocomplete="off">
            <textarea id="mtext" rows="1" maxlength="{{ max_len }}" placeholder="Write a message..." aria-label="Message"></textarea>
            <button class="btn" type="submit">Send</button>
        </form>
    </main>

</div>

<script>
(function() {
"use strict";

const boot = JSON.parse(document.getElementById("boot").textContent);
const CSRF = boot.csrf;
const ME = boot.me;

let theme = boot.theme;
let rooms = [];
let online = new Set();
let current = "public";
let lastId = 0;
let loaded = false;
let epoch = 0;
let polling = false;
let pollAgain = false;
let netOk = true;
let seen = {};

const seenKey = "chat_seen_" + ME.toLowerCase();

try { seen = JSON.parse(localStorage.getItem(seenKey) || "{}"); } catch (e) { seen = {}; }

localStorage.setItem("chat_theme", JSON.stringify(theme));
applyTheme(theme.preset, theme.accent);

const $ = function(id) { return document.getElementById(id); };
const ICONS = {public: "\u{1F310}", group: "\u{1F465}", private_group: "\u{1F512}", dm: "\u{1F4AC}"};

/* ---------- tiny helpers ---------- */

function el(tag, props) {
    const e = document.createElement(tag);

    if (props) {
        Object.keys(props).forEach(function(k) {
            const v = props[k];

            if (k === "class") e.className = v;
            else if (k === "text") e.textContent = v;
            else if (k.indexOf("on") === 0) e.addEventListener(k.slice(2), v);
            else e.setAttribute(k, v);
        });
    }

    for (let i = 2; i < arguments.length; i++) {
        const kids = [].concat(arguments[i]);

        kids.forEach(function(c) {
            if (c === null || c === undefined || c === false) return;
            e.append(c.nodeType ? c : document.createTextNode(c));
        });
    }

    return e;
}

function hue(s) {
    let h = 0;
    for (const c of s) h = (h * 31 + c.codePointAt(0)) % 360;
    return h;
}

function avatar(name, isOnline) {
    const first = Array.from(name)[0] || "?";
    const a = el("div", {class: "av", text: first.toUpperCase()});
    a.style.background = "hsl(" + hue(name) + " 48% 42%)";
    if (isOnline) a.append(el("i", {class: "on"}));
    return a;
}

function iconAvatar(type) {
    return el("div", {class: "av icon", text: ICONS[type] || "\u{1F4AC}"});
}

let toastTimer;
function toast(text) {
    let t = $("toast");
    if (!t) { t = el("div", {id: "toast", role: "status"}); document.body.append(t); }
    t.textContent = text;
    t.hidden = false;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(function() { t.hidden = true; }, 3200);
}

async function api(path, opts) {
    opts = opts || {};
    const o = {method: opts.method || "GET", headers: {"X-CSRF-Token": CSRF}};

    if (opts.body !== undefined) {
        o.method = "POST";
        o.headers["Content-Type"] = "application/json";
        o.body = JSON.stringify(opts.body);
    }

    const r = await fetch(path, o);
    const d = await r.json().catch(function() { return {}; });

    if (r.status === 401) { location.href = "/login"; return null; }
    if (r.status === 403 && d.error === "must_change") { location.href = "/change-password"; return null; }
    if (!r.ok) throw new Error(d.error || "Something went wrong.");

    return d;
}

function fmtTs(ts) {
    const d = new Date(ts * 1000);
    const t = d.toLocaleTimeString([], {hour: "numeric", minute: "2-digit"});

    if (d.toDateString() === new Date().toDateString()) return t;
    return d.toLocaleDateString([], {day: "numeric", month: "short"}) + ", " + t;
}

function roomById(id) {
    return rooms.find(function(r) { return r.id === id; });
}

function markSeen() {
    if (lastId > (seen[current] || 0)) {
        seen[current] = lastId;
        localStorage.setItem(seenKey, JSON.stringify(seen));
    }
}

/* ---------- sidebar ---------- */

function renderRooms() {
    const list = $("roomlist");
    list.textContent = "";

    const sections = [
        [null, function(r) { return r.type === "public"; }],
        ["Groups", function(r) { return r.type === "group" && r.joined; }],
        ["Private groups", function(r) { return r.type === "private_group"; }],
        ["Direct messages", function(r) { return r.type === "dm"; }],
        ["Discover groups", function(r) { return r.type === "group" && !r.joined; }]
    ];

    sections.forEach(function(sec) {
        const items = rooms.filter(sec[1]).sort(function(a, b) { return b.updated - a.updated; });

        if (!items.length) return;
        if (sec[0]) list.append(el("div", {class: "sec", text: sec[0]}));

        items.forEach(function(r) {
            let av;

            if (r.type === "dm") av = avatar(r.name, online.has(r.name));
            else av = iconAvatar(r.type);

            const unread = r.joined && r.id !== current && r.last_seq > (seen[r.id] || 0);
            const meta = r.count !== null ? r.count + (r.count === 1 ? " member" : " members") : "";

            const row = el("button", {
                class: "room" + (r.id === current ? " active" : ""),
                type: "button",
                onclick: function() { r.joined ? openRoom(r.id) : joinRoom(r); }
            },
                av,
                el("div", {class: "nm"}, r.name, r.type === "group" || r.type === "private_group" ? el("div", {class: "meta", text: meta}) : null),
                unread ? el("i", {class: "unread", title: "New messages"}) : null,
                !r.joined ? el("span", {class: "meta", text: "Join"}) : null
            );

            list.append(row);
        });
    });
}

function renderHeader() {
    const r = roomById(current);
    if (!r) return;

    $("rtitle").textContent = r.name;

    let sub = "";
    if (r.type === "public") sub = "Everyone \u00b7 " + online.size + " online";
    else if (r.type === "group") sub = "Group \u00b7 " + r.count + " members";
    else if (r.type === "private_group") sub = "Private group \u00b7 " + r.count + " members";
    else sub = online.has(r.name) ? "Direct message \u00b7 online" : "Direct message";

    if (!netOk) sub += " \u00b7 reconnecting...";
    $("rsub").textContent = sub;

    $("infoBtn").hidden = !(r.type === "group" || r.type === "private_group");
}

/* ---------- messages ---------- */

function addMessages(list) {
    const box = $("msgs");
    const nearBottom = box.scrollHeight - box.scrollTop - box.clientHeight < 90;
    const showNames = (roomById(current) || {}).type !== "dm";

    if (!loaded) {
        box.textContent = "";
        if (!list.length) box.append(el("div", {class: "empty", id: "emptyMsg", text: "No messages yet. Say hi!"}));
    }

    if (list.length && $("emptyMsg")) $("emptyMsg").remove();

    list.forEach(function(m) {
        lastId = Math.max(lastId, m.id);

        box.append(el("div", {class: "msg" + (m.mine ? " mine" : "")},
            !m.mine && showNames ? el("div", {class: "who", text: m.u}) : null,
            el("div", {class: "bubble", text: m.t}),
            el("div", {class: "ts", text: fmtTs(m.ts)})
        ));
    });

    if (!loaded || (list.length && nearBottom)) box.scrollTop = box.scrollHeight;

    loaded = true;
    markSeen();
}

function openRoom(id) {
    current = id;
    lastId = 0;
    loaded = false;

    $("msgs").textContent = "";
    $("msgs").append(el("div", {class: "empty", text: "Loading..."}));
    $("sidebar").classList.remove("open");

    renderRooms();
    renderHeader();
    poll();
}

async function refreshRooms() {
    const d = await api("/api/poll");
    if (!d) return;
    rooms = d.rooms;
    online = new Set(d.online);
    renderRooms();
    renderHeader();
}

async function poll() {
    if (polling) { pollAgain = true; return; }
    polling = true;

    const rid = current;

    try {
        const d = await api("/api/poll?room=" + encodeURIComponent(rid) + "&after=" + lastId);
        if (!d) return;

        netOk = true;
        rooms = d.rooms;
        online = new Set(d.online);

        if (rid === current) {
            if (!d.room_ok) {
                if (current !== "public") {
                    toast("That chat is no longer available.");
                    setTimeout(function() { openRoom("public"); }, 0);
                    return;
                }
            } else if (loaded && d.epoch !== epoch) {
                // chat was cleared by the owner: reload it fresh
                setTimeout(function() { openRoom(current); }, 0);
                return;
            } else {
                epoch = d.epoch;
                addMessages(d.messages);
            }
        }

        renderRooms();
        renderHeader();
    } catch (e) {
        netOk = false;
        renderHeader();
    } finally {
        polling = false;

        if (pollAgain) {
            pollAgain = false;
            poll();
        }
    }
}

function loop() {
    poll().finally(function() {
        setTimeout(loop, document.hidden ? 8000 : 2500);
    });
}

document.addEventListener("visibilitychange", function() { if (!document.hidden) poll(); });

/* ---------- composer ---------- */

const ta = $("mtext");

function autosize() {
    ta.style.height = "auto";
    ta.style.height = Math.min(ta.scrollHeight, 120) + "px";
}

ta.addEventListener("input", autosize);

ta.addEventListener("keydown", function(e) {
    const touch = window.matchMedia("(pointer: coarse)").matches;

    if (e.key === "Enter" && !e.shiftKey && !e.isComposing && !touch) {
        e.preventDefault();
        $("composer").requestSubmit();
    }
});

$("composer").addEventListener("submit", async function(e) {
    e.preventDefault();

    const text = ta.value.trim();
    if (!text) return;

    ta.value = "";
    autosize();

    try {
        await api("/api/rooms/" + encodeURIComponent(current) + "/messages", {body: {text: text}});
        poll();
    } catch (err) {
        ta.value = text;
        autosize();
        toast(err.message);
    }
});

/* ---------- modal ---------- */

function openModal(title, content) {
    const scrim = el("div", {class: "scrim"});
    const box = el("div", {class: "modal", role: "dialog", "aria-modal": "true", "aria-label": title});

    function onKey(e) { if (e.key === "Escape") close(); }
    function close() { scrim.remove(); document.removeEventListener("keydown", onKey); }

    box.append(
        el("div", {class: "mhead"},
            el("h2", {text: title}),
            el("button", {class: "icon-btn", type: "button", "aria-label": "Close", text: "\u2715", onclick: close})
        ),
        el("div", {class: "mbody"}, content)
    );

    scrim.addEventListener("mousedown", function(e) { if (e.target === scrim) close(); });
    scrim.append(box);
    document.body.append(scrim);
    document.addEventListener("keydown", onKey);

    return close;
}

function userPicker(users, options) {
    const multi = !!options.multi;
    const exclude = options.exclude || [];
    const selected = new Set();
    const search = el("input", {type: "search", placeholder: "Search people...", "aria-label": "Search people"});
    const list = el("div", {class: "ulist"});

    function draw() {
        const q = search.value.trim().toLowerCase();
        const shown = users.filter(function(u) {
            return exclude.indexOf(u.name) === -1 && u.name.toLowerCase().indexOf(q) !== -1;
        });

        list.textContent = "";

        if (!shown.length) {
            list.append(el("div", {class: "muted pad", text: users.length ? "No matching people." : "No other accounts yet."}));
            return;
        }

        shown.forEach(function(u) {
            const row = multi
                ? el("label", {class: "urow"})
                : el("button", {class: "urow", type: "button"});

            if (multi) {
                const cb = el("input", {type: "checkbox"});
                cb.checked = selected.has(u.name);
                cb.addEventListener("change", function() {
                    if (cb.checked) selected.add(u.name); else selected.delete(u.name);
                });
                row.append(cb);
            } else {
                row.addEventListener("click", function() { options.onPick(u.name); });
            }

            row.append(avatar(u.name, u.online), el("span", {class: "nm", text: u.name}));
            list.append(row);
        });
    }

    search.addEventListener("input", draw);
    draw();

    return {node: el("div", null, search, list), selected: selected};
}

/* ---------- new DM / group ---------- */

async function openNewDm() {
    const d = await api("/api/users");
    if (!d) return;

    let close;

    const picker = userPicker(d.users, {
        multi: false,
        onPick: async function(name) {
            try {
                const r = await api("/api/dm", {body: {user: name}});
                close();
                await refreshRooms();
                openRoom(r.id);
            } catch (e) { toast(e.message); }
        }
    });

    close = openModal("New direct message", el("div", null,
        el("p", {class: "muted", text: "Only you and the other person can see this chat."}),
        picker.node
    ));
}

async function openNewGroup(kind) {
    const priv = kind === "private_group";
    const d = await api("/api/users");
    if (!d) return;

    const name = el("input", {maxlength: "40", placeholder: priv ? "Private group name" : "Group name", "aria-label": "Group name"});
    const picker = userPicker(d.users, {multi: true});
    const err = el("div", {class: "err"});
    const btn = el("button", {class: "btn block", type: "button", text: "Create"});

    const close = openModal(priv ? "New private group" : "New group", el("div", null,
        el("p", {class: "muted", text: priv
            ? "Only people you add can see or join this group."
            : "Anyone can find and join this group. You can add people now too."}),
        name,
        el("div", {class: "lbl", text: "Add people"}),
        picker.node,
        err,
        btn
    ));

    btn.addEventListener("click", async function() {
        err.textContent = "";

        try {
            const r = await api("/api/rooms", {body: {type: kind, name: name.value, members: Array.from(picker.selected)}});
            close();
            await refreshRooms();
            openRoom(r.id);
        } catch (e) { err.textContent = e.message; }
    });

    name.focus();
}

async function joinRoom(r) {
    try {
        await api("/api/rooms/" + encodeURIComponent(r.id) + "/join", {body: {}});
        await refreshRooms();
        openRoom(r.id);
    } catch (e) { toast(e.message); }
}

/* ---------- room info ---------- */

async function openRoomInfo() {
    const rid = current;
    const info = await api("/api/rooms/" + encodeURIComponent(rid) + "/info");
    if (!info) return;

    const box = el("div");
    let close;

    box.append(el("p", {class: "muted", text: info.type === "private_group"
        ? "Private group. Only members can see it."
        : "Group. Anyone can find and join it."}));

    box.append(el("div", {class: "lbl", text: "Members (" + info.members.length + ")"}));

    const ul = el("div", {class: "ulist"});

    info.members.forEach(function(m) {
        const row = el("div", {class: "urow"},
            avatar(m.name, m.online),
            el("span", {class: "nm", text: m.name + (m.owner ? " (owner)" : "")})
        );

        if (info.is_owner && !m.owner) {
            row.append(el("button", {class: "btn small danger", type: "button", text: "Remove", onclick: async function() {
                try {
                    await api("/api/rooms/" + encodeURIComponent(rid) + "/remove", {body: {user: m.name}});
                    close();
                    openRoomInfo();
                } catch (e) { toast(e.message); }
            }}));
        }

        ul.append(row);
    });

    box.append(ul);

    if (info.is_owner) {
        box.append(el("button", {class: "btn block ghost", type: "button", text: "Add people", onclick: async function() {
            const d = await api("/api/users");
            if (!d) return;

            const existing = info.members.map(function(m) { return m.name; });
            const picker = userPicker(d.users, {multi: true, exclude: existing});
            const err = el("div", {class: "err"});
            const go = el("button", {class: "btn block", type: "button", text: "Add selected"});

            close();

            const close2 = openModal("Add people", el("div", null, picker.node, err, go));

            go.addEventListener("click", async function() {
                try {
                    await api("/api/rooms/" + encodeURIComponent(rid) + "/add", {body: {users: Array.from(picker.selected)}});
                    close2();
                    await refreshRooms();
                    openRoomInfo();
                } catch (e) { err.textContent = e.message; }
            });
        }}));

        box.append(el("button", {class: "btn block danger", type: "button", text: "Delete group", onclick: async function() {
            if (!confirm("Delete this group and all its messages?")) return;

            try {
                await api("/api/rooms/" + encodeURIComponent(rid) + "/delete", {body: {}});
                close();
                await refreshRooms();
                openRoom("public");
            } catch (e) { toast(e.message); }
        }}));
    } else {
        box.append(el("button", {class: "btn block danger", type: "button", text: "Leave group", onclick: async function() {
            if (!confirm("Leave this group?")) return;

            try {
                await api("/api/rooms/" + encodeURIComponent(rid) + "/leave", {body: {}});
                close();
                await refreshRooms();
                openRoom("public");
            } catch (e) { toast(e.message); }
        }}));
    }

    close = openModal(info.name, box);
}

/* ---------- settings (theme + account) ---------- */

const ACCENTS = ["#2563eb", "#0ea5e9", "#14b8a6", "#16a34a", "#eab308", "#f97316", "#ef4444", "#ec4899", "#8b5cf6", "#64748b"];
let saveTimer;

function markThemeActive() {
    document.querySelectorAll(".tchip").forEach(function(b) {
        b.classList.toggle("active", b.dataset.preset === theme.preset);
    });

    document.querySelectorAll(".acc").forEach(function(b) {
        b.classList.toggle("active", b.dataset.color.toLowerCase() === theme.accent.toLowerCase());
    });
}

function setTheme(preset, accent) {
    theme = {preset: preset, accent: accent};
    applyTheme(preset, accent);
    localStorage.setItem("chat_theme", JSON.stringify(theme));

    clearTimeout(saveTimer);
    saveTimer = setTimeout(function() {
        api("/api/theme", {body: theme}).catch(function() {});
    }, 400);

    markThemeActive();
}

function openSettings() {
    const box = el("div");

    box.append(el("div", {class: "lbl", text: "Theme"}));
    box.append(el("p", {class: "muted", text: "Dark or soft light colours. Saved to your account."}));

    const grid = el("div", {class: "themes"});

    Object.keys(THEMES).forEach(function(key) {
        const t = THEMES[key];
        const chip = el("button", {class: "tchip", type: "button", "data-preset": key, onclick: function() { setTheme(key, theme.accent); }},
            (function() {
                const sw = el("div", {class: "sw"}, el("i"), el("i"), el("i"));
                const kids = sw.children;
                kids[0].style.background = t.bg;
                kids[1].style.background = t.panel;
                kids[2].style.background = t.bubble;
                return sw;
            })(),
            el("span", {text: t.name})
        );
        grid.append(chip);
    });

    box.append(grid);

    box.append(el("div", {class: "lbl", text: "Accent colour"}));

    const accents = el("div", {class: "accents"});

    ACCENTS.forEach(function(c) {
        const b = el("button", {class: "acc", type: "button", "data-color": c, "aria-label": "Accent " + c, onclick: function() { setTheme(theme.preset, c); }});
        b.style.background = c;
        accents.append(b);
    });

    const custom = el("input", {type: "color", class: "custom", value: theme.accent, "aria-label": "Custom colour"});
    custom.addEventListener("input", function() { setTheme(theme.preset, custom.value); });
    accents.append(custom);

    box.append(accents);

    box.append(el("div", {class: "lbl", text: "Account"}));
    box.append(el("div", null, "Username: ", el("b", {text: ME}), el("div", {class: "muted", text: "Your username can't be changed."})));

    box.append(el("a", {href: "/change-password", text: "Change password"}));

    const form = el("form", {method: "POST", action: "/logout"},
        el("input", {type: "hidden", name: "csrf_token", value: CSRF}),
        el("button", {class: "btn block danger", type: "submit", text: "Log out"})
    );
    box.append(form);

    openModal("Settings", box);
    markThemeActive();
}

/* ---------- wire up ---------- */

$("meAv").replaceWith(avatar(ME, true));
$("meName").textContent = ME;

$("newDm").addEventListener("click", openNewDm);
$("newGroup").addEventListener("click", function() { openNewGroup("group"); });
$("newPrivate").addEventListener("click", function() { openNewGroup("private_group"); });
$("settingsBtn").addEventListener("click", openSettings);
$("infoBtn").addEventListener("click", openRoomInfo);
$("menuBtn").addEventListener("click", function() { $("sidebar").classList.add("open"); });
$("sscrim").addEventListener("click", function() { $("sidebar").classList.remove("open"); });

openRoom("public");
loop();

})();
</script>

</body>
</html>
"""


# =========================================================
# ADMIN / OWNER DASHBOARD (one template, owner sees extra tools)
# =========================================================

STAFF_HTML = r"""
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{{ title }}</title>
<style>
{{ base_css|safe }}

:root { --accent: {{ default_accent }}; --on-accent: #ffffff; }

body { background: #0b1020; height: auto; }

.container { max-width: 980px; margin: auto; padding: 20px; }

.card {
    background: #172033;
    border-radius: 16px;
    padding: 18px;
    margin-bottom: 15px;
}

.card h2 { margin: 0 0 10px; font-size: 18px; }
h1 { margin: 0 0 4px; }
.subtitle { color: var(--muted); margin: 0; font-size: 14px; }

.top-bar { display: flex; justify-content: space-between; align-items: flex-start; flex-wrap: wrap; gap: 10px; }

.stat { display: inline-block; background: #26344d; padding: 12px 14px; border-radius: 12px; margin: 10px 8px 0 0; }

.table-wrap { overflow-x: auto; }
table { width: 100%; border-collapse: collapse; }
th, td { padding: 9px 10px; border-bottom: 1px solid #2b3a55; text-align: left; vertical-align: middle; }
th { color: var(--muted); font-size: 13px; font-weight: 600; }

.user-row { display: flex; align-items: center; gap: 10px; }
.avatar {
    width: 28px; height: 28px; border-radius: 50%;
    background: var(--accent); color: var(--on-accent);
    display: flex; align-items: center; justify-content: center;
    font-weight: 700; font-size: 12px; flex-shrink: 0;
}

.online { color: #4ade80; }
.offline { color: var(--muted); }

.actions { display: flex; gap: 6px; flex-wrap: wrap; }
form.inline { margin: 0; }

.notice {
    background: color-mix(in srgb, var(--accent) 18%, #172033);
    border: 1px solid var(--accent);
}
.notice code {
    font-size: 20px; font-weight: 700; letter-spacing: .5px;
    background: #0b1020; padding: 4px 10px; border-radius: 8px;
}

.swatches { display: flex; gap: 10px; margin-top: 10px; }
.swatch { width: 30px; height: 30px; border-radius: 50%; padding: 0; border: 2px solid transparent; cursor: pointer; }
.swatch.active { border-color: #fff; }

@media (max-width: 650px) {
    .hide-sm { display: none; }
}
</style>
</head>
<body>

<div class="container">

<div class="card">
    <div class="top-bar">
        <div>
            <h1>{{ heading }}</h1>
            <p class="subtitle">
                {% if is_owner %}Owner-only control panel.{% else %}Help users with account problems and keep chats tidy.{% endif %}
                Private chats and private groups are never shown here.
            </p>
        </div>
        <a href="{{ url_for('staff_logout', role=role) }}">Logout</a>
    </div>

    <div class="stat">Accounts: <b>{{ accounts|length }}</b></div>
    <div class="stat">Online now: <b>{{ online_count }}</b></div>
    <div class="stat">Groups: <b>{{ groups|length }}</b></div>
    <div class="stat">Messages stored: <b>{{ message_count }}</b></div>
    {% if is_owner %}<div class="stat">Admin sessions: <b>{{ admins|length }}</b></div>{% endif %}
</div>


{% if notice %}
<div class="card notice">
    <h2>Temporary password ready</h2>
    <p>
        For <b>{{ notice.user }}</b>:
        <code id="tempPw">{{ notice.temp }}</code>
        <button class="btn small" type="button" onclick="copyTemp()">Copy</button>
    </p>
    <p class="subtitle">
        Give this to the user privately. It works for {{ temp_hours }} hours, and they must choose a new password when they log in.
        It is shown only here; the real password can never be viewed.
    </p>
    <form class="inline" method="POST" action="{{ url_for('staff_dismiss_notice', role=role) }}">
        <input type="hidden" name="csrf_token" value="{{ csrf_token }}">
        <button class="btn small ghost" type="submit">Done, hide it</button>
    </form>
</div>
{% endif %}


<div class="card">
    <b>Theme colour</b>
    <div class="subtitle">Saved only on this device/browser.</div>
    <div class="swatches">
        {% for c in ['#2563eb', '#16a34a', '#7c3aed', '#ea580c', '#0891b2'] %}
        <button type="button" class="swatch" data-color="{{ c }}" style="background:{{ c }}" onclick="setAccent('{{ c }}')" aria-label="Accent {{ c }}"></button>
        {% endfor %}
    </div>
</div>


<div class="card">
    <h2>Password / ID help requests</h2>

    {% if requests %}
    <div class="table-wrap">
    <table>
        <tr>
            <th>Username they typed</th>
            <th>Note</th>
            <th class="hide-sm">Asked at</th>
            <th>Action</th>
        </tr>
        {% for r in requests %}
        <tr>
            <td>{{ r.guess or '(not given)' }}</td>
            <td>{{ r.note or '-' }}</td>
            <td class="hide-sm">{{ r.when }}</td>
            <td>
                <div class="actions">
                {% if r.match_id %}
                <form class="inline" method="POST" action="{{ url_for('staff_reset', role=role, uid=r.match_id) }}" onsubmit="return confirm('Make a new temporary password for this account?');">
                    <input type="hidden" name="csrf_token" value="{{ csrf_token }}">
                    <button class="btn small" type="submit">Reset password</button>
                </form>
                {% else %}
                <span class="subtitle">No exact match - find them in Accounts below</span>
                {% endif %}
                <form class="inline" method="POST" action="{{ url_for('staff_dismiss_request', role=role, rid=r.id) }}">
                    <input type="hidden" name="csrf_token" value="{{ csrf_token }}">
                    <button class="btn small ghost" type="submit">Dismiss</button>
                </form>
                </div>
            </td>
        </tr>
        {% endfor %}
    </table>
    </div>
    {% else %}
    <p class="subtitle">No pending requests.</p>
    {% endif %}
</div>


<div class="card">
    <h2>Accounts</h2>

    {% if accounts %}
    <div class="table-wrap">
    <table>
        <tr>
            <th>Username</th>
            <th>Status</th>
            <th class="hide-sm">Joined</th>
            <th>Action</th>
        </tr>
        {% for a in accounts %}
        <tr>
            <td>
                <div class="user-row">
                    <div class="avatar">{{ a.username[0]|upper }}</div>
                    {{ a.username }}
                </div>
            </td>
            <td>
                {% if a.online %}<span class="online">&#9679; Online</span>{% else %}<span class="offline">Offline</span>{% endif %}
                {% if a.must_change %}<div class="subtitle">waiting for new password</div>{% endif %}
            </td>
            <td class="hide-sm">{{ a.created }}</td>
            <td>
                <div class="actions">
                    <form class="inline" method="POST" action="{{ url_for('staff_reset', role=role, uid=a.id) }}" data-name="{{ a.username }}" onsubmit="return confirm('Make a new temporary password for ' + this.dataset.name + '?');">
                        <input type="hidden" name="csrf_token" value="{{ csrf_token }}">
                        <button class="btn small" type="submit">Reset password</button>
                    </form>
                    {% if a.online %}
                    <form class="inline" method="POST" action="{{ url_for('staff_kick', role=role, uid=a.id) }}" onsubmit="return confirm('Log this user out?');">
                        <input type="hidden" name="csrf_token" value="{{ csrf_token }}">
                        <button class="btn small ghost" type="submit">Kick</button>
                    </form>
                    {% endif %}
                    {% if is_owner %}
                    <form class="inline" method="POST" action="{{ url_for('owner_delete_user', uid=a.id) }}" onsubmit="return confirm('Delete this account permanently?');">
                        <input type="hidden" name="csrf_token" value="{{ csrf_token }}">
                        <button class="btn small danger" type="submit">Delete</button>
                    </form>
                    {% endif %}
                </div>
            </td>
        </tr>
        {% endfor %}
    </table>
    </div>
    {% else %}
    <p class="subtitle">No accounts yet.</p>
    {% endif %}
</div>


<div class="card">
    <h2>Groups</h2>

    {% if groups %}
    <div class="table-wrap">
    <table>
        <tr>
            <th>Name</th>
            <th>Type</th>
            <th>Members</th>
            <th class="hide-sm">Owner</th>
            <th>Action</th>
        </tr>
        {% for g in groups %}
        <tr>
            <td>{{ g.name }}</td>
            <td>{{ 'Private' if g.private else 'Public' }}</td>
            <td>{{ g.count }}</td>
            <td class="hide-sm">{{ g.owner }}</td>
            <td>
                <form class="inline" method="POST" action="{{ url_for('staff_delete_room', role=role, rid=g.id) }}" onsubmit="return confirm('Delete this group and its messages?');">
                    <input type="hidden" name="csrf_token" value="{{ csrf_token }}">
                    <button class="btn small danger" type="submit">Delete</button>
                </form>
            </td>
        </tr>
        {% endfor %}
    </table>
    </div>
    {% else %}
    <p class="subtitle">No groups yet.</p>
    {% endif %}
</div>


{% if is_owner %}

<div class="card">
    <h2>Active admin sessions</h2>

    {% if admins %}
    <div class="table-wrap">
    <table>
        <tr><th>Admin</th><th>Action</th></tr>
        {% for adm in admins %}
        <tr>
            <td>Normal Admin</td>
            <td>
                <form class="inline" method="POST" action="{{ url_for('remove_admin', admin_sid=adm.sid) }}">
                    <input type="hidden" name="csrf_token" value="{{ csrf_token }}">
                    <button class="btn small danger" type="submit">Remove admin</button>
                </form>
            </td>
        </tr>
        {% endfor %}
    </table>
    </div>
    {% else %}
    <p class="subtitle">No active admin sessions.</p>
    {% endif %}
</div>

<div class="card">
    <h2>Chat moderation</h2>
    <div class="actions">
        <form class="inline" method="POST" action="{{ url_for('owner_clear', scope='public') }}" onsubmit="return confirm('Clear the public chat?');">
            <input type="hidden" name="csrf_token" value="{{ csrf_token }}">
            <button class="btn danger" type="submit">Clear public chat</button>
        </form>
        <form class="inline" method="POST" action="{{ url_for('owner_clear', scope='all') }}" onsubmit="return confirm('Clear messages in EVERY chat (public, groups and DMs)?');">
            <input type="hidden" name="csrf_token" value="{{ csrf_token }}">
            <button class="btn danger" type="submit">Clear all chats</button>
        </form>
    </div>
</div>

{% endif %}

</div>

<script>

const LOGOUT_URL = "{{ url_for('staff_logout', role=role) }}";
const STAFF_CSRF = "{{ csrf_token }}";
const ACCENT_KEY = "{{ role }}_theme_accent";
const HAS_NOTICE = {{ 'true' if notice else 'false' }};

function textOn(hex) {
    const n = parseInt(hex.slice(1), 16);
    const lum = (0.299 * (n >> 16 & 255) + 0.587 * (n >> 8 & 255) + 0.114 * (n & 255)) / 255;
    return lum > 0.62 ? "#111827" : "#ffffff";
}

function paintAccent(color) {
    document.documentElement.style.setProperty("--accent", color);
    document.documentElement.style.setProperty("--on-accent", textOn(color));
    document.querySelectorAll(".swatch").forEach(function(el) {
        el.classList.toggle("active", el.dataset.color === color);
    });
}

function setAccent(color) {
    localStorage.setItem(ACCENT_KEY, color);
    paintAccent(color);
}

paintAccent(localStorage.getItem(ACCENT_KEY) || "{{ default_accent }}");

function copyTemp() {
    const text = document.getElementById("tempPw").textContent;

    if (navigator.clipboard) {
        navigator.clipboard.writeText(text);
    }
}

// ---- Auto-logout when leaving this page ----
// Our own background refresh and our own form submits set
// plannedReload first, so they do NOT log you out. Closing the
// tab, going elsewhere, or a manual browser refresh does.

let plannedReload = false;

document.addEventListener("submit", function(e) {
    if (!e.defaultPrevented) plannedReload = true;
});

window.addEventListener("pagehide", function() {
    if (!plannedReload) {
        const data = new URLSearchParams();
        data.append("csrf_token", STAFF_CSRF);
        navigator.sendBeacon(LOGOUT_URL, data);
    }
});

// Refresh every 5s, except while a temporary password is on screen
// (so it can be copied calmly).
if (!HAS_NOTICE) {
    setTimeout(function() {
        plannedReload = true;
        location.reload();
    }, 5000);
}

</script>

</body>
</html>
"""


app.config["MAX_CONTENT_LENGTH"] = 64 * 1024


# =========================================================
# ACCOUNT ROUTES
# =========================================================

def auth_page(mode, title, action, subtitle=None, error=None, ok=None,
              values=None, forced=False):
    return render_template_string(
        AUTH_HTML,
        mode=mode, title=title, action=action, subtitle=subtitle,
        error=error, ok=ok, values=values or {}, forced=forced,
        csrf_token=get_csrf_token(),
        base_css=BASE_CSS, theme_js=THEME_JS
    )


@app.route("/")
def index():
    with LOCK:
        cleanup()
        user = current_user()

        if not user:
            return redirect(url_for("login"))

        if user.get("must_change"):
            return redirect(url_for("change_password"))

        PRESENCE[ukey(user["username"])] = now()

        boot = {
            "me": user["username"],
            "csrf": get_csrf_token(),
            "theme": user.get("theme") or DEFAULT_THEME,
        }

        return render_template_string(
            CHAT_HTML, boot=boot, max_len=MAX_MESSAGE_LENGTH,
            base_css=BASE_CSS, theme_js=THEME_JS
        )


@app.route("/login", methods=["GET", "POST"])
def login():
    with LOCK:
        cleanup()

        if current_user():
            return redirect(url_for("index"))

        ip = get_client_ip()
        page = lambda **kw: auth_page(
            "login", "Log in", url_for("login"),
            subtitle="Welcome back.", **kw
        )

        if is_locked_out(ip):
            return page(error=f"Too many failed attempts. Try again in {lockout_remaining(ip)}s.")

        if request.method == "POST":
            if not csrf_valid():
                return page(error="Session expired, please try again.")

            username = request.form.get("username", "")
            password = request.form.get("password", "")

            k = ukey(username)
            user = DB["users"].get(k)

            # Always run one hash check so timing doesn't reveal
            # whether the username exists.
            stored = user["pw_hash"] if user else DUMMY_HASH
            valid = check_password_hash(stored, password) and user is not None

            if valid:
                until = user.get("temp_until")

                if user.get("must_change") and until and now() > until:
                    return page(
                        error="This temporary password has expired. Ask the admin for a new one.",
                        values={"username": username}
                    )

                register_successful_login(ip)
                login_session(k)
                return redirect(url_for("index"))

            register_failed_login(ip)
            return page(error="Wrong username or password.", values={"username": username})

        return page()


@app.route("/register", methods=["GET", "POST"])
def register():
    with LOCK:
        cleanup()

        if current_user():
            return redirect(url_for("index"))

        page = lambda **kw: auth_page(
            "register", "Create account", url_for("register"),
            subtitle="One account per person. Your chats stay private to you.", **kw
        )

        if request.method == "POST":
            if not csrf_valid():
                return page(error="Session expired, please try again.")

            username = request.form.get("username", "")
            password = request.form.get("password", "")
            confirm = request.form.get("confirm", "")

            name, error = check_username(username)

            if not error:
                error = check_password(password)

            if not error and password != confirm:
                error = "Passwords do not match."

            if error:
                return page(error=error, values={"username": username})

            if not throttle_hit("register", get_client_ip(), 5, 3600):
                return page(error="Too many accounts created from this network. Try again later.",
                            values={"username": username})

            k = ukey(name)

            DB["users"][k] = {
                "id": uuid.uuid4().hex[:12],
                "username": name,
                "pw_hash": generate_password_hash(password),
                "created": now(),
                "pw_ver": 1,
                "must_change": False,
                "temp_until": None,
                "theme": dict(DEFAULT_THEME),
            }

            save_db()
            login_session(k)
            return redirect(url_for("index"))

        return page()


@app.route("/forgot", methods=["GET", "POST"])
def forgot():
    with LOCK:
        cleanup()

        page = lambda **kw: auth_page(
            "forgot", "Forgot username or password",
            url_for("forgot"),
            subtitle="Send a request to the admin/owner. They will give you a temporary password.",
            **kw
        )

        if request.method == "POST":
            if not csrf_valid():
                return page(error="Session expired, please try again.")

            guess = " ".join((request.form.get("username") or "").split())[:MAX_USERNAME_LENGTH]
            note = " ".join((request.form.get("note") or "").split())[:200]
            values = {"username": guess, "note": note}

            if not guess and not note:
                return page(error="Write the username you remember, or a short note, so the admin can find you.",
                            values=values)

            if not throttle_hit("forgot", get_client_ip(), 3, 3600):
                return page(error="Too many requests. Please wait a while and try again.", values=values)

            duplicate = guess and any(
                not r.get("done") and ukey(r.get("guess", "")) == ukey(guess)
                for r in DB["recovery"]
            )

            if not duplicate:
                DB["recovery"].append({
                    "id": uuid.uuid4().hex[:10],
                    "guess": guess,
                    "note": note,
                    "ts": now(),
                    "done": False,
                })

                del DB["recovery"][:-200]
                save_db()

            return auth_page(
                "sent", "Request sent", url_for("forgot"),
                ok="Your request was sent. When the admin or owner resets your password, "
                   "they will give you a temporary password. Log in with it and choose a new password."
            )

        return page()


@app.route("/change-password", methods=["GET", "POST"])
def change_password():
    with LOCK:
        user = current_user()

        if not user:
            return redirect(url_for("login"))

        forced = bool(user.get("must_change"))
        k = ukey(user["username"])

        page = lambda **kw: auth_page(
            "change", "Set a new password" if forced else "Change password",
            url_for("change_password"),
            subtitle="Your temporary password worked. Choose your own password to continue." if forced else None,
            forced=forced, **kw
        )

        if request.method == "POST":
            if not csrf_valid():
                return page(error="Session expired, please try again.")

            current = request.form.get("current", "")
            new = request.form.get("password", "")
            confirm = request.form.get("confirm", "")

            if not forced:
                if not throttle_hit("chpw", k, 5, 300):
                    return page(error="Too many attempts. Please wait a few minutes.")

                if not check_password_hash(user["pw_hash"], current):
                    return page(error="Current password is wrong.")

            error = check_password(new)

            if not error and new != confirm:
                error = "Passwords do not match."

            if not error and check_password_hash(user["pw_hash"], new):
                error = "Please choose a password different from the old one."

            if error:
                return page(error=error)

            user["pw_hash"] = generate_password_hash(new)
            user["pw_ver"] += 1
            user["must_change"] = False
            user["temp_until"] = None
            save_db()

            # Other devices are logged out; this one stays in.
            session["pv"] = user["pw_ver"]
            return redirect(url_for("index"))

        return page()


@app.route("/logout", methods=["POST"])
def logout():
    if csrf_valid():
        session.pop("uk", None)
        session.pop("pv", None)

    return redirect(url_for("login"))


# =========================================================
# JSON API
# =========================================================

def fail(message, code=400):
    return jsonify(error=message), code


def get_room(rid):
    return DB["rooms"].get(rid)


@app.route("/api/poll")
@api
def api_poll(user):
    k = ukey(user["username"])

    out = {
        "rooms": visible_rooms(k),
        "online": [display_name(x) for x in PRESENCE if x in DB["users"] and is_online(x)],
        "messages": [],
        "room_ok": False,
        "epoch": 0,
    }

    rid = request.args.get("room")
    room = get_room(rid) if rid else None

    if room and can_read(room, k):
        try:
            after = int(request.args.get("after", "0"))
        except ValueError:
            after = 0

        msgs = DB["messages"].get(rid, [])
        chosen = [m for m in msgs if m["id"] > after] if after > 0 else msgs[-100:]

        out["room_ok"] = True
        out["epoch"] = room.get("epoch", 0)
        out["messages"] = [
            {"id": m["id"], "u": m["u"], "t": m["t"], "ts": m["ts"], "mine": m["k"] == k}
            for m in chosen
        ]

    return jsonify(out)


@app.route("/api/users")
@api
def api_users(user):
    me = ukey(user["username"])

    people = [
        {"name": u["username"], "online": is_online(k)}
        for k, u in DB["users"].items() if k != me
    ]

    people.sort(key=lambda p: p["name"].casefold())
    return jsonify(users=people)


@app.route("/api/theme", methods=["POST"])
@api
def api_theme(user):
    data = body()
    preset = data.get("preset")
    accent = data.get("accent")

    if preset not in THEME_PRESETS or not isinstance(accent, str) or not HEX_COLOR.match(accent):
        return fail("Invalid theme.")

    user["theme"] = {"preset": preset, "accent": accent.lower()}
    save_db()
    return jsonify(ok=True)


@app.route("/api/rooms", methods=["POST"])
@api
def api_create_room(user):
    k = ukey(user["username"])
    data = body()

    kind = data.get("type")

    if kind not in ("group", "private_group"):
        return fail("Invalid group type.")

    name = " ".join(str(data.get("name", "")).split())

    if len(name) < 2:
        return fail("Group name must be at least 2 characters.")

    if len(name) > MAX_ROOM_NAME_LENGTH:
        return fail(f"Group name must be {MAX_ROOM_NAME_LENGTH} characters or less.")

    if not name.isprintable():
        return fail("Group name contains invalid characters.")

    owned = sum(1 for r in DB["rooms"].values() if r.get("owner") == k)

    if owned >= MAX_ROOMS_PER_USER:
        return fail(f"You can own up to {MAX_ROOMS_PER_USER} groups.")

    members = [k]
    wanted = data.get("members")

    if isinstance(wanted, list):
        for n in wanted[:MAX_GROUP_MEMBERS]:
            mk = ukey(n)

            if mk in DB["users"] and mk not in members:
                members.append(mk)

    rid = uuid.uuid4().hex[:12]

    DB["rooms"][rid] = {
        "id": rid, "type": kind, "name": name, "owner": k,
        "members": members, "created": now(), "updated": now(), "seq": 0,
    }
    DB["messages"][rid] = []

    save_db()
    return jsonify(id=rid)


@app.route("/api/dm", methods=["POST"])
@api
def api_dm(user):
    k = ukey(user["username"])
    pk = ukey(body().get("user", ""))

    if pk == k:
        return fail("You can't message yourself.")

    if pk not in DB["users"]:
        return fail("That account doesn't exist.", 404)

    rid = dm_room_id(k, pk)

    if rid not in DB["rooms"]:
        DB["rooms"][rid] = {
            "id": rid, "type": "dm", "name": "", "owner": None,
            "members": [k, pk], "created": now(), "updated": now(), "seq": 0,
        }
        DB["messages"][rid] = []
        save_db()

    return jsonify(id=rid)


@app.route("/api/rooms/<rid>/join", methods=["POST"])
@api
def api_join(user, rid):
    k = ukey(user["username"])
    room = get_room(rid)

    if not room or room["type"] != "group":
        return fail("This group can't be joined.", 404)

    if k not in room["members"]:
        if len(room["members"]) >= MAX_GROUP_MEMBERS:
            return fail("This group is full.")

        room["members"].append(k)
        save_db()

    return jsonify(ok=True)


@app.route("/api/rooms/<rid>/leave", methods=["POST"])
@api
def api_leave(user, rid):
    k = ukey(user["username"])
    room = get_room(rid)

    if not room or room["type"] not in ("group", "private_group") or k not in room["members"]:
        return fail("You are not in this group.", 404)

    if room.get("owner") == k:
        return fail("Owners can't leave. Delete the group instead.")

    room["members"].remove(k)
    save_db()
    return jsonify(ok=True)


@app.route("/api/rooms/<rid>/delete", methods=["POST"])
@api
def api_delete_room(user, rid):
    k = ukey(user["username"])
    room = get_room(rid)

    if not room or room["type"] not in ("group", "private_group"):
        return fail("Group not found.", 404)

    if room.get("owner") != k:
        return fail("Only the group owner can do this.", 403)

    delete_room(rid)
    save_db()
    return jsonify(ok=True)


@app.route("/api/rooms/<rid>/add", methods=["POST"])
@api
def api_add_members(user, rid):
    k = ukey(user["username"])
    room = get_room(rid)

    if not room or room["type"] not in ("group", "private_group"):
        return fail("Group not found.", 404)

    if room.get("owner") != k:
        return fail("Only the group owner can add people.", 403)

    wanted = body().get("users")
    added = 0

    if isinstance(wanted, list):
        for n in wanted[:MAX_GROUP_MEMBERS]:
            mk = ukey(n)

            if mk in DB["users"] and mk not in room["members"] and len(room["members"]) < MAX_GROUP_MEMBERS:
                room["members"].append(mk)
                added += 1

    if not added:
        return fail("Pick at least one person to add.")

    save_db()
    return jsonify(ok=True)


@app.route("/api/rooms/<rid>/remove", methods=["POST"])
@api
def api_remove_member(user, rid):
    k = ukey(user["username"])
    room = get_room(rid)

    if not room or room["type"] not in ("group", "private_group"):
        return fail("Group not found.", 404)

    if room.get("owner") != k:
        return fail("Only the group owner can remove people.", 403)

    target = ukey(body().get("user", ""))

    if target == k:
        return fail("You can't remove yourself.")

    if target in room["members"]:
        room["members"].remove(target)
        save_db()

    return jsonify(ok=True)


@app.route("/api/rooms/<rid>/info")
@api
def api_room_info(user, rid):
    k = ukey(user["username"])
    room = get_room(rid)

    if not room or room["type"] not in ("group", "private_group") or k not in room["members"]:
        return fail("Group not found.", 404)

    members = [
        {"name": display_name(m), "online": is_online(m), "owner": m == room.get("owner")}
        for m in room["members"]
    ]

    members.sort(key=lambda m: (not m["owner"], m["name"].casefold()))

    return jsonify(
        id=rid, name=room["name"], type=room["type"],
        is_owner=room.get("owner") == k, members=members
    )


@app.route("/api/rooms/<rid>/messages", methods=["POST"])
@api
def api_send(user, rid):
    k = ukey(user["username"])
    room = get_room(rid)

    if not room or not can_read(room, k):
        return fail("Chat not found.", 404)

    text = body().get("text")

    if not isinstance(text, str) or not text.strip():
        return fail("Message is empty.")

    if not throttle_hit("msg", k, 6, 5):
        return fail("You're sending messages too fast.")

    room["seq"] += 1
    room["updated"] = now()

    msgs = DB["messages"].setdefault(rid, [])
    msgs.append({
        "id": room["seq"], "k": k, "u": user["username"],
        "t": text.strip()[:MAX_MESSAGE_LENGTH], "ts": now(),
    })

    del msgs[:-MAX_STORED_PER_ROOM]

    save_db()
    return jsonify(ok=True)


# =========================================================
# ADMIN / OWNER
# =========================================================

STAFF_INFO = {
    "admin": {"title": "Admin Login", "heading": "Admin Dashboard", "accent": "#2563eb", "key": "admin_sid"},
    "owner": {"title": "Owner Login", "heading": "Owner Dashboard", "accent": "#7c3aed", "key": "owner_sid"},
}

STAFF_ROLE = "<any(admin,owner):role>"


def staff_session(role):
    return admin_sessions.get(session.get(STAFF_INFO[role]["key"]))


def require_role(role):
    """True if this browser holds a live admin/owner session for `role`."""
    key = STAFF_INFO[role]["key"]
    sid = session.get(key)

    if not sid:
        return False

    data = admin_sessions.get(sid)

    if not data:
        session.pop(key, None)
        return False

    if data["role"] != role:
        return False

    if now() - data["last_seen"] > STAFF_TIMEOUT:
        admin_sessions.pop(sid, None)
        session.pop(key, None)
        return False

    data["last_seen"] = now()
    return True


def staff_action_ok(role):
    return require_role(role) and csrf_valid()


def find_user_by_id(uid):
    for k, u in DB["users"].items():
        if u.get("id") == uid:
            return k, u

    return None, None


def render_staff(role):
    is_owner = role == "owner"
    sd = staff_session(role)

    accounts = []

    for k, u in DB["users"].items():
        accounts.append({
            "id": u["id"],
            "username": u["username"],
            "online": is_online(k),
            "created": fmt_time(u["created"]),
            "must_change": bool(u.get("must_change")),
        })

    accounts.sort(key=lambda a: a["username"].casefold())

    requests = []

    for r in reversed(DB["recovery"]):
        if r.get("done"):
            continue

        match_k = ukey(r["guess"]) if r.get("guess") else None
        match = DB["users"].get(match_k) if match_k else None

        requests.append({
            "id": r["id"],
            "guess": r.get("guess", ""),
            "note": r.get("note", ""),
            "when": fmt_time(r["ts"]),
            "match_id": match["id"] if match else None,
        })

    groups = [
        {
            "id": r["id"], "name": r["name"], "private": r["type"] == "private_group",
            "count": len(r["members"]), "owner": display_name(r["owner"]),
        }
        for r in DB["rooms"].values() if r["type"] in ("group", "private_group")
    ]

    admins = [{"sid": sid} for sid, d in admin_sessions.items() if d["role"] == "admin"]

    return render_template_string(
        STAFF_HTML,
        role=role, is_owner=is_owner,
        title=STAFF_INFO[role]["heading"], heading=STAFF_INFO[role]["heading"],
        default_accent=STAFF_INFO[role]["accent"],
        accounts=accounts, requests=requests, groups=groups, admins=admins,
        online_count=sum(1 for a in accounts if a["online"]),
        message_count=sum(len(m) for m in DB["messages"].values()),
        notice=sd.get("notice") if sd else None,
        temp_hours=TEMP_PASSWORD_HOURS,
        csrf_token=get_csrf_token(),
        base_css=BASE_CSS
    )


def staff_login_page(role, error=None):
    return auth_page(
        "staff", STAFF_INFO[role]["title"],
        url_for("staff_home", role=role), error=error
    )


@app.route(f"/{STAFF_ROLE}", methods=["GET", "POST"], strict_slashes=False)
def staff_home(role):
    with LOCK:
        cleanup()

        if require_role(role):
            return render_staff(role)

        ip = get_client_ip()

        if is_locked_out(ip):
            return staff_login_page(
                role, f"Too many failed attempts. Try again in {lockout_remaining(ip)}s."
            )

        if request.method == "POST":
            if not csrf_valid():
                return staff_login_page(role, "Session expired, please try again.")

            password = request.form.get("password", "")
            expected = OWNER_PASSWORD if role == "owner" else ADMIN_PASSWORD

            if safe_equal(password.strip(), expected):
                register_successful_login(ip)

                sid = str(uuid.uuid4())
                admin_sessions[sid] = {"role": role, "created": now(), "last_seen": now()}
                session[STAFF_INFO[role]["key"]] = sid

                return redirect(url_for("staff_home", role=role))

            register_failed_login(ip)
            print(f"[login] wrong {role} password from {ip} "
                  f"(typed {len(password.strip())} characters)")
            return staff_login_page(role, "Wrong password.")

        return staff_login_page(role)


@app.route(f"/{STAFF_ROLE}/logout", methods=["GET", "POST"])
def staff_logout(role):
    with LOCK:
        sid = session.pop(STAFF_INFO[role]["key"], None)

        if sid:
            admin_sessions.pop(sid, None)

    # POST comes from the silent "leaving page" beacon, which
    # can't follow redirects.
    if request.method == "POST":
        return ("", 204)

    return redirect(url_for("staff_home", role=role))


@app.route(f"/{STAFF_ROLE}/kick/<uid>", methods=["POST"])
def staff_kick(role, uid):
    with LOCK:
        if staff_action_ok(role):
            k, user = find_user_by_id(uid)

            if user:
                user["pw_ver"] += 1        # logs their sessions out
                PRESENCE.pop(k, None)
                save_db()

        return redirect(url_for("staff_home", role=role))


@app.route(f"/{STAFF_ROLE}/reset/<uid>", methods=["POST"])
def staff_reset(role, uid):
    with LOCK:
        if staff_action_ok(role):
            k, user = find_user_by_id(uid)

            if user:
                temp = secrets.token_urlsafe(6)

                user["pw_hash"] = generate_password_hash(temp)
                user["pw_ver"] += 1
                user["must_change"] = True
                user["temp_until"] = now() + TEMP_PASSWORD_HOURS * 3600
                PRESENCE.pop(k, None)

                for req in DB["recovery"]:
                    if req.get("guess") and ukey(req["guess"]) == k:
                        req["done"] = True

                save_db()

                staff_session(role)["notice"] = {"user": user["username"], "temp": temp}

        return redirect(url_for("staff_home", role=role))


@app.route(f"/{STAFF_ROLE}/dismiss-notice", methods=["POST"])
def staff_dismiss_notice(role):
    with LOCK:
        if staff_action_ok(role):
            staff_session(role).pop("notice", None)

        return redirect(url_for("staff_home", role=role))


@app.route(f"/{STAFF_ROLE}/dismiss/<rid>", methods=["POST"])
def staff_dismiss_request(role, rid):
    with LOCK:
        if staff_action_ok(role):
            for req in DB["recovery"]:
                if req["id"] == rid:
                    req["done"] = True

            save_db()

        return redirect(url_for("staff_home", role=role))


@app.route(f"/{STAFF_ROLE}/delete-room/<rid>", methods=["POST"])
def staff_delete_room(role, rid):
    with LOCK:
        if staff_action_ok(role):
            room = get_room(rid)

            # Only groups. DMs and message contents are never managed here.
            if room and room["type"] in ("group", "private_group"):
                delete_room(rid)
                save_db()

        return redirect(url_for("staff_home", role=role))


# ---------------- owner-only ----------------

@app.route("/owner/delete-user/<uid>", methods=["POST"])
def owner_delete_user(uid):
    with LOCK:
        if staff_action_ok("owner"):
            k, user = find_user_by_id(uid)

            if user:
                delete_account(k)
                save_db()

        return redirect(url_for("staff_home", role="owner"))


@app.route("/owner/remove_admin/<admin_sid>", methods=["POST"])
def remove_admin(admin_sid):
    with LOCK:
        if staff_action_ok("owner"):
            data = admin_sessions.get(admin_sid)

            # Only genuine admin sessions, never an owner session.
            if data and data.get("role") == "admin":
                admin_sessions.pop(admin_sid, None)

        return redirect(url_for("staff_home", role="owner"))


@app.route("/owner/clear/<any(public,all):scope>", methods=["POST"])
def owner_clear(scope):
    with LOCK:
        if staff_action_ok("owner"):
            for rid, room in DB["rooms"].items():
                if scope == "all" or rid == "public":
                    DB["messages"][rid] = []
                    room["epoch"] = room.get("epoch", 0) + 1

            save_db()

        return redirect(url_for("staff_home", role="owner"))


# =========================================================
# MAIN
# =========================================================

if __name__ == "__main__":

    print("-" * 56)
    print(f"Owner password: {OWNER_SOURCE}"
          + (" (OWNER123)" if OWNER_SOURCE == "DEFAULT" else f" ({len(OWNER_PASSWORD)} characters)"))
    print(f"Admin password: {ADMIN_SOURCE}"
          + (" (ADMIN123)" if ADMIN_SOURCE == "DEFAULT" else f" ({len(ADMIN_PASSWORD)} characters)"))

    if "DEFAULT" in (OWNER_SOURCE, ADMIN_SOURCE):
        print("WARNING: change the DEFAULT password(s) before going live.")

    print("-" * 56)

    app.run(
        host="0.0.0.0",
        port=int(os.environ.get("PORT", 5000)),
        debug=False,
        threaded=True
    )
