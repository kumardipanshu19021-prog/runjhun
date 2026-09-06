import asyncio, csv, html, logging, os, sqlite3, tempfile, time, uuid, zipfile, shutil, sys, threading
try:
    import fcntl
except ImportError:
    fcntl = None
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import quote, urlparse
from contextlib import contextmanager
from datetime import datetime, timedelta
from pathlib import Path
from types import SimpleNamespace

import telegram
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup as TelegramMarkup
from telegram.constants import ParseMode, ChatAction
from telegram.error import TelegramError, RetryAfter, Forbidden
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, MessageHandler, filters, ContextTypes, ConversationHandler, ChatJoinRequestHandler, ChatMemberHandler

BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
try: ADMIN_ID = int(os.getenv("ADMIN_ID", "0").strip())
except ValueError: ADMIN_ID = 0
try: OWNER_ID = int(os.getenv("OWNER_ID", str(ADMIN_ID)).strip())
except ValueError: OWNER_ID = ADMIN_ID
DB_PATH = os.getenv("DB_PATH", "bot2.db").strip() or "bot2.db"
BACKUP_DIR = Path(os.getenv("BACKUP_DIR", "backups")); BACKUP_DIR.mkdir(parents=True, exist_ok=True)
BOT_VERSION, DB_VERSION = "4.4.0", 8
STARTED_AT = time.monotonic()
LAST_ERROR = ""
ERROR_LOG_MAX = 200
BROADCAST_TASK = None
BROADCAST_LOCK = asyncio.Lock()
AUTO_BACKUP_TASK = None
PREMIUM_EMOJI_ENABLED = True
HTTP_SERVER = None
HTTP_SERVER_THREAD = None
INSTANCE_LOCK_FILE = None
INSTANCE_LOCK_FH = None
CONFLICT_SHUTDOWN = False

BTN1, BTN2, BTN3 = "🎯 Claim Agent", "📊 Statistics", "🤝 Refer & Earn"
EMOJI = {"🎯": "5228855127892327218", "📊": "6093382540784046658", "🤝": "6086990448331592466", "📣": "6095891759462617671", "💬": "6095865895169560113", "📝": "6010292709066019210", "🖼️": "5341285075210224047", "➕": "6093406373557571574", "❌": "6010471186432005118", "⚙️": "6010355840790303830", "✅": "6246537187614005254", "🌟": "5783170625090622777", "📌": "6089019283508040459", "🔔": "6093852083788715042", "👑": "6247039939305808563", "💰": "5785325680765965100"}

logging.basicConfig(format="%(asctime)s - %(levelname)s - %(message)s", level=logging.INFO)
logger = logging.getLogger("force_join_bot")

# Conversation states
(S_CH_ID,S_CH_NAME,S_CH_LINK,S_WELCOME,S_WELCOME_PHOTO,S_POSTJOIN,S_TOP,S_BTN1,S_BTN2,S_BTN3,
 S_BCAST,S_RESTORE,S_SEARCH,S_USERMSG,S_EDITNAME,S_EDITLINK,S_EMOJI,S_BTN_NAME,S_BTN_NORMAL,S_BTN_PREMIUM,S_FORCE_JOIN_MSG,
 S_BCAST_BTN_ASK,S_BCAST_BTN_LINK,S_BCAST_BTN_NAME,S_BCAST_BTN_STYLE,S_BCAST_PREVIEW)=range(26)

@contextmanager
def db():
    c=sqlite3.connect(DB_PATH, timeout=30, check_same_thread=False)
    try:
        c.execute("PRAGMA busy_timeout=30000"); c.execute("PRAGMA journal_mode=WAL"); c.execute("PRAGMA synchronous=NORMAL")
        yield c; c.commit()
    except Exception:
        c.rollback(); raise
    finally: c.close()

def esc(x): return html.escape(str(x or ""))
def scalar(sql,args=(),default=0):
    try:
        with db() as c:
            r=c.execute(sql,args).fetchone()
            return r[0] if r else default
    except Exception as e:
        logger.error("DB scalar: %s",e); return default

def gset(k,d=""):
    try:
        with db() as c:
            r=c.execute("SELECT value FROM settings WHERE key=?",(k,)).fetchone()
            return r[0] if r else d
    except Exception as e:
        logger.error("gset %s: %s",k,e); return d

def sset(k,v):
    with db() as c: c.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)",(k,str(v)))

def log_error(level,msg):
    global LAST_ERROR
    LAST_ERROR=str(msg)[:2000]
    try:
        with db() as c:
            c.execute("INSERT INTO error_logs(created_at,level,message) VALUES(?,?,?)",(datetime.now().isoformat(),level,str(msg)[:2000]))
            c.execute("DELETE FROM error_logs WHERE id NOT IN (SELECT id FROM error_logs ORDER BY id DESC LIMIT ?)",(ERROR_LOG_MAX,))
    except Exception: pass

class DBHandler(logging.Handler):
    def emit(self,record):
        if record.levelno>=logging.ERROR: log_error(record.levelname,record.getMessage())
logger.addHandler(DBHandler())

def _clean_visible_label(value):
    value=_remove_invisible_chars(value).strip()
    return value

def _sanitize_button_config_rows(conn):
    """Repair invalid legacy button labels without overwriting valid custom labels."""
    import json
    for key,default in BUTTON_DEFAULTS.items():
        setting_key=BUTTON_CONFIG_PREFIX+key
        row=conn.execute("SELECT value FROM settings WHERE key=?",(setting_key,)).fetchone()
        cfg=_config_from_json(row[0]) if row and row[0] else None
        if not isinstance(cfg,dict):
            cfg=dict(default)
        merged=dict(default)
        merged.update(cfg)

        raw_label=merged.get("label",default.get("label",""))
        label=_clean_visible_label(raw_label)
        if key.startswith("ui_join_channel"):
            if not label:
                label=default["label"]
        elif not label or not safe_button_text(label):
            label=default["label"]
        merged["label"]=label

        pe=str(merged.get("premium_emoji_id",default.get("premium_emoji_id","")) or "").strip()
        merged["premium_emoji_id"]=pe if pe.isdigit() else ""
        merged["premium_enabled"]=bool(merged.get("premium_enabled",default.get("premium_enabled",True)))
        merged["style"]=merged.get("style") if merged.get("style") in BUTTON_STYLES else default["style"]
        try:
            merged["position"]=max(1,int(merged.get("position",default.get("position",1)) or default.get("position",1)))
        except (TypeError,ValueError):
            merged["position"]=default.get("position",1)
        merged["enabled"]=bool(merged.get("enabled",default.get("enabled",True)))
        merged["callback_data"]=default["callback_data"]
        merged["url"]=default.get("url")
        conn.execute(
            "INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)",
            (setting_key,_config_to_json(merged))
        )

def sanitize_database_values(conn):
    """Repair legacy DB values that could create invisible Telegram buttons."""
    # Channel names: preserve valid user content; repair blank/invisible values deterministically.
    rows=conn.execute("SELECT id,channel_id,channel_name FROM channels").fetchall()
    for cid,channel_id,name in rows:
        clean=_clean_visible_label(name)
        if not clean:
            clean=f"Channel {str(channel_id).strip() or cid}"
        conn.execute("UPDATE channels SET channel_name=? WHERE id=?",(clean,cid))

    _sanitize_button_config_rows(conn)

    # Keep legacy force-join emoji settings coherent with repaired button configs.
    for key,default_key in (
        ("join_channel_premium_emoji_id","ui_join_channel"),
        ("joined_button_premium_emoji_id","ui_join_check"),
    ):
        cfg=_config_from_json((conn.execute("SELECT value FROM settings WHERE key=?",(BUTTON_CONFIG_PREFIX+default_key,)).fetchone() or [""])[0]) or {}
        eid=str(cfg.get("premium_emoji_id","") or "")
        conn.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)",(key,eid))

def migrate_force_join_message_setting(conn):
    """Create the dedicated Force Join message without importing legacy welcome/top text."""
    row=conn.execute("SELECT value FROM settings WHERE key='force_join_message'").fetchone()
    if not row:
        conn.execute("INSERT INTO settings(key,value) VALUES('force_join_message','')")
    elif row[0] is None:
        conn.execute("UPDATE settings SET value='' WHERE key='force_join_message'")

def migrate_force_join_legacy_state(conn):
    """Idempotently neutralize legacy Force Join state without touching business data."""
    legacy_keys=(
        "old_force_join_message","join_message","welcome_join_message",
        "force_join_instruction","legacy_force_join","start_message",
    )
    placeholders=",".join("?" for _ in legacy_keys)
    conn.execute(f"DELETE FROM settings WHERE key IN ({placeholders})",legacy_keys)
    conn.execute("""
        UPDATE join_requests
        SET status=CASE
            WHEN lower(COALESCE(status,''))='active' THEN 'pending'
            WHEN lower(COALESCE(status,''))='joined' THEN 'legacy_verified'
            WHEN lower(COALESCE(status,'')) IN
                ('pending','approved','declined','cancelled','verified','legacy_verified')
                THEN lower(status)
            ELSE 'pending'
        END
    """)
    conn.execute("""
        DELETE FROM join_requests
        WHERE user_id NOT IN (SELECT user_id FROM users)
           OR channel_id NOT IN (SELECT channel_id FROM channels)
    """)

def init_db():
    with db() as c:
        c.executescript("""
        CREATE TABLE IF NOT EXISTS users(user_id INTEGER PRIMARY KEY,first_name TEXT DEFAULT '',username TEXT DEFAULT '',joined_at TEXT NOT NULL,status TEXT NOT NULL DEFAULT 'active');
        CREATE TABLE IF NOT EXISTS channels(id INTEGER PRIMARY KEY AUTOINCREMENT,channel_id TEXT UNIQUE NOT NULL,channel_name TEXT NOT NULL,channel_link TEXT NOT NULL,position INTEGER DEFAULT 0,order_num INTEGER DEFAULT 0,enabled INTEGER NOT NULL DEFAULT 1);
        CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY,value TEXT);
        CREATE TABLE IF NOT EXISTS join_requests(user_id INTEGER NOT NULL,channel_id TEXT NOT NULL,requested_at TEXT,status TEXT DEFAULT 'active',PRIMARY KEY(user_id,channel_id));
        CREATE TABLE IF NOT EXISTS broadcast_msgs(bcast_id TEXT NOT NULL,user_id INTEGER NOT NULL,message_id INTEGER NOT NULL);
        CREATE TABLE IF NOT EXISTS broadcasts(bcast_id TEXT PRIMARY KEY,created_at TEXT,source_chat_id INTEGER,source_message_id INTEGER,kind TEXT,total INTEGER DEFAULT 0,sent INTEGER DEFAULT 0,failed INTEGER DEFAULT 0,cancelled INTEGER DEFAULT 0,status TEXT DEFAULT 'running',last_error TEXT DEFAULT '',button_url TEXT DEFAULT '',button_label TEXT DEFAULT '',button_style TEXT DEFAULT '');
        CREATE TABLE IF NOT EXISTS error_logs(id INTEGER PRIMARY KEY AUTOINCREMENT,created_at TEXT,level TEXT,message TEXT);
        CREATE TABLE IF NOT EXISTS referrals(referral_id INTEGER PRIMARY KEY AUTOINCREMENT,user_id INTEGER UNIQUE NOT NULL,referrer_id INTEGER NOT NULL,created_at TEXT NOT NULL);
        """)
        cols={r[1] for r in c.execute("PRAGMA table_info(broadcasts)")}
        if "button_url" not in cols: c.execute("ALTER TABLE broadcasts ADD COLUMN button_url TEXT DEFAULT ''")
        if "button_label" not in cols: c.execute("ALTER TABLE broadcasts ADD COLUMN button_label TEXT DEFAULT ''")
        if "button_style" not in cols: c.execute("ALTER TABLE broadcasts ADD COLUMN button_style TEXT DEFAULT ''")
        # Migrate original schema safely.
        cols={r[1] for r in c.execute("PRAGMA table_info(users)")}
        if "username" not in cols: c.execute("ALTER TABLE users ADD COLUMN username TEXT DEFAULT ''")
        if "status" not in cols: c.execute("ALTER TABLE users ADD COLUMN status TEXT NOT NULL DEFAULT 'active'")
        cols={r[1] for r in c.execute("PRAGMA table_info(channels)")}
        if "enabled" not in cols: c.execute("ALTER TABLE channels ADD COLUMN enabled INTEGER NOT NULL DEFAULT 1")
        cols={r[1] for r in c.execute("PRAGMA table_info(join_requests)")}
        if "requested_at" not in cols: c.execute("ALTER TABLE join_requests ADD COLUMN requested_at TEXT")
        if "status" not in cols: c.execute("ALTER TABLE join_requests ADD COLUMN status TEXT DEFAULT 'active'")
        c.execute("UPDATE join_requests SET requested_at=COALESCE(requested_at,?)",(datetime.now().isoformat(),))
        defaults={
          # Force Join text is stored separately; empty is a valid configuration.
          "welcome":"",
          "welcome_photo":"","postjoin":"🏛️ <b>Welcome!</b>\n\n📋 <b>Rules</b>\n• One agent per user\n• Permanent assignment","top":"",
          "btn1_msg":"🎯 Agent claim coming soon!","btn2_msg":"📊 Statistics coming soon!","btn3_msg":"🤝 Refer & Earn coming soon!",
          "maintenance_mode":"0","force_join_enabled":"1","welcome_photo_enabled":"1","broadcast_enabled":"1","auto_backup_enabled":"0",
          "auto_backup_frequency":"daily","auto_backup_keep":"7","debug_logging":"0","last_backup":"","last_restore":"",
          "button_style_btn1":"primary","button_style_btn2":"success","button_style_btn3":"primary",
          "button_emoji_btn1":EMOJI["🎯"],"button_emoji_btn2":EMOJI["📊"],"button_emoji_btn3":EMOJI["🤝"],
          "button_emoji_enabled_btn1":"1","button_emoji_enabled_btn2":"1","button_emoji_enabled_btn3":"1",
          "premium_emoji_system_enabled":"1",
          "join_channel_premium_emoji_id":EMOJI["📣"],
          "joined_button_label":"Joined",
          "joined_button_premium_emoji_id":EMOJI["✅"],
        }
        for k,v in defaults.items(): c.execute("INSERT OR IGNORE INTO settings(key,value) VALUES(?,?)",(k,str(v)))
        migrate_force_join_message_setting(c)
        migrate_force_join_legacy_state(c)
        migrate_button_configs(c)
        sanitize_database_values(c)

def control_ids():
    ids=set()
    if ADMIN_ID: ids.add(ADMIN_ID)
    if OWNER_ID: ids.add(OWNER_ID)
    return ids

def is_admin(uid): return bool(uid in control_ids())
def is_owner(uid): return bool(OWNER_ID and uid==OWNER_ID)

def add_user(u):
    with db() as c:
        old=c.execute("SELECT 1 FROM users WHERE user_id=?",(u.id,)).fetchone()
        if old:
            c.execute("UPDATE users SET first_name=?,username=? WHERE user_id=?",(u.first_name or "",u.username or "",u.id)); return False
        c.execute("INSERT INTO users VALUES(?,?,?,?,?)",(u.id,u.first_name or "",u.username or "",datetime.now().isoformat(),"active")); return True

def user_status(uid): return scalar("SELECT status FROM users WHERE user_id=?",(uid,),"active")
def set_status(uid,status):
    with db() as c:c.execute("UPDATE users SET status=? WHERE user_id=?",(status,uid))
def delete_user(uid):
    with db() as c:
        c.execute("DELETE FROM users WHERE user_id=?",(uid,)); c.execute("DELETE FROM join_requests WHERE user_id=?",(uid,))

def users(include_blocked=False):
    with db() as c:
        q="SELECT user_id FROM users" if include_blocked else "SELECT user_id FROM users WHERE status!='blocked'"
        return [r[0] for r in c.execute(q)]

def search_users(q):
    q=str(q).strip()
    with db() as c:
        if q.isdigit(): return c.execute("SELECT user_id,first_name,username,joined_at,status FROM users WHERE user_id=?",(int(q),)).fetchall()
        x=f"%{q}%"; return c.execute("SELECT user_id,first_name,username,joined_at,status FROM users WHERE first_name LIKE ? OR username LIKE ? LIMIT 25",(x,x)).fetchall()

def channels(all_rows=True):
    with db() as c:
        q="SELECT id,channel_id,channel_name,channel_link,position,order_num,enabled FROM channels ORDER BY order_num,id"
        if not all_rows:q=q.replace(" ORDER BY"," WHERE enabled=1 ORDER BY")
        return c.execute(q).fetchall()
def channel(cid):
    with db() as c:return c.execute("SELECT id,channel_id,channel_name,channel_link,position,order_num,enabled FROM channels WHERE id=?",(cid,)).fetchone()
def add_channel(cid,name,link):
    clean_name=_clean_visible_label(name)
    if not clean_name:
        raise ValueError("Channel name cannot be empty.")
    clean_id=str(cid).strip()
    if not clean_id:
        raise ValueError("Channel ID cannot be empty.")
    clean_link=str(link or "").strip()
    with db() as c:
        n=c.execute("SELECT COALESCE(MAX(order_num),0) FROM channels").fetchone()[0]+1
        c.execute("INSERT INTO channels(channel_id,channel_name,channel_link,order_num,enabled) VALUES(?,?,?, ?,1)",(clean_id,clean_name,clean_link,n))
def update_channel(cid,name=None,link=None):
    with db() as c:
        if name is not None:
            clean_name=_clean_visible_label(name)
            if not clean_name:
                raise ValueError("Channel name cannot be empty.")
            c.execute("UPDATE channels SET channel_name=? WHERE id=?",(clean_name,cid))
        if link is not None:c.execute("UPDATE channels SET channel_link=? WHERE id=?",(link,cid))
def delete_channel(cid):
    with db() as c:c.execute("DELETE FROM channels WHERE id=?",(cid,))
def toggle_channel(cid):
    with db() as c:c.execute("UPDATE channels SET enabled=1-enabled WHERE id=?",(cid,))
def move_channel(cid,direction):
    rows=channels(True); ids=[r[0] for r in rows]
    if cid not in ids:return
    i=ids.index(cid); j=i-1 if direction=="left" else i+1
    if j<0 or j>=len(ids):return
    with db() as c:
        c.execute("UPDATE channels SET order_num=? WHERE id=?",(rows[j][5],rows[i][0]))
        c.execute("UPDATE channels SET order_num=? WHERE id=?",(rows[i][5],rows[j][0]))

def record_req(uid,cid):
    with db() as c:
        c.execute("INSERT OR REPLACE INTO join_requests(user_id,channel_id,requested_at,status) VALUES(?,?,?,?)",(uid,str(cid),datetime.now().isoformat(),"pending"))

def mark_req(uid,cid):
    with db() as c:
        c.execute("UPDATE join_requests SET status='verified' WHERE user_id=? AND channel_id=?",(uid,str(cid)))

def has_req(uid,cid):
    # Compatibility only. A request is never membership proof.
    return bool(scalar("SELECT 1 FROM join_requests WHERE user_id=? AND channel_id=? AND status IN ('pending','approved','verified')",(uid,str(cid)),0))

def get_request_status(uid,cid):
    try:
        with db() as c:
            row=c.execute(
                "SELECT status FROM join_requests WHERE user_id=? AND channel_id=?",
                (uid,str(cid))).fetchone()
        return str(row[0]).lower() if row and row[0] else None
    except Exception as e:
        logger.warning("Join request status lookup failed user=%s channel=%s: %s",uid,cid,e)
        return None


async def verify_channel_membership(bot,user_id,channel_id):
    cid=str(channel_id).strip()
    result={"state":"unknown","is_member":False,"request_pending":False,"error":None}
    try:
        m=await bot.get_chat_member(cid,user_id)
        status=str(getattr(m,"status","") or "").lower()
        if status in ("member","administrator","creator", "restricted"):
            result.update(state=status,is_member=True)
        elif status=="left":
            result["state"]="left"
        elif status in ("kicked","banned"):
            result["state"]="kicked"
        elif status in ("pending","join_request"):
            result.update(state="pending",request_pending=True,is_member=True)
        else:
            result["state"]="unknown"
        return result
    except Exception as e:
        result.update(state="api_error",error=str(e))
        return result


async def verify_required_channels(bot,user_id,rows=None):
    """Check every enabled required channel exactly once per verification cycle."""
    rows=channels(False) if rows is None else [r for r in rows if r[6]]
    joined=set();remaining=[];results=[];all_verified=True
    for r in rows:
        cid=str(r[1]).strip()
        if not cid:
            all_verified=False
            remaining.append(r)
            results.append({"channel":r,"channel_id":cid,"state":"unknown",
                            "is_member":False,"request_pending":False,"error":"empty channel id"})
            continue
        result=await verify_channel_membership(bot,user_id,cid)
        result["channel"]=r
        results.append(result)
        if result["is_member"]:
            joined.add(cid)
            mark_req(user_id,cid)
        else:
            all_verified=False
            remaining.append(r)
    logger.info("ForceJoin verification cycle user=%s all_verified=%s remaining_channels=%s",
                user_id,all_verified,[str(r[1]) for r in remaining])
    return {"all_verified":all_verified,"joined":joined,"remaining":remaining,"results":results}


async def check_joined(bot,uid):
    """Backward-compatible wrapper; DB requests never participate in membership proof."""
    if is_admin(uid) or gset("force_join_enabled","1")!="1":
        return True,set()
    rows=channels(False)
    if not rows:
        return True,set()
    v=await verify_required_channels(bot,uid,rows)
    return v["all_verified"],v["joined"]

async def channel_status(bot,cid):
    try:
        me=await bot.get_me(); ch=await bot.get_chat(cid); m=await bot.get_chat_member(cid,me.id)
        return True,m.status in ("administrator","creator"),ch.title or str(cid),m.status
    except TelegramError as e:return False,False,str(e),"error"

# ---------------------------------------------------------------------------
# Centralized button configuration / rendering
# ---------------------------------------------------------------------------
BUTTON_DEFAULTS = {
    "btn1": {"label":"Claim Agent", "normal_emoji":"🎯", "premium_emoji_id":EMOJI["🎯"], "premium_enabled":True, "style":"primary", "callback_data":"btn1", "url":None, "position":1, "enabled":True},
    "btn2": {"label":"Statistics", "normal_emoji":"📊", "premium_emoji_id":EMOJI["📊"], "premium_enabled":True, "style":"success", "callback_data":"btn2", "url":None, "position":2, "enabled":True},
    "btn3": {"label":"Refer & Earn", "normal_emoji":"🤝", "premium_emoji_id":EMOJI["🤝"], "premium_enabled":True, "style":"primary", "callback_data":"btn3", "url":None, "position":3, "enabled":True},
    "ui_a_dash": {"label":"Dashboard", "normal_emoji":"📊", "premium_emoji_id":EMOJI["📊"], "premium_enabled":True, "style":"primary", "callback_data":"a_dash", "url":None, "position":1, "enabled":True},
    "ui_a_chs": {"label":"Channels", "normal_emoji":"📢", "premium_emoji_id":EMOJI["📣"], "premium_enabled":True, "style":"primary", "callback_data":"a_chs", "url":None, "position":2, "enabled":True},
    "ui_a_msgs": {"label":"Messages", "normal_emoji":"📝", "premium_emoji_id":EMOJI["📝"], "premium_enabled":True, "style":"primary", "callback_data":"a_msgs", "url":None, "position":3, "enabled":True},
    "ui_a_buttons": {"label":"Buttons", "normal_emoji":"🎨", "premium_emoji_id":EMOJI["🌟"], "premium_enabled":True, "style":"success", "callback_data":"a_buttons", "url":None, "position":4, "enabled":True},
    "ui_a_bcast": {"label":"Broadcast", "normal_emoji":"📣", "premium_emoji_id":EMOJI["📣"], "premium_enabled":True, "style":"success", "callback_data":"a_bcast", "url":None, "position":5, "enabled":True},
    "ui_a_members": {"label":"Members", "normal_emoji":"👥", "premium_emoji_id":EMOJI["👑"], "premium_enabled":True, "style":"primary", "callback_data":"a_members", "url":None, "position":6, "enabled":True},
    "ui_a_backup_menu": {"label":"Backup Center", "normal_emoji":"💾", "premium_emoji_id":EMOJI["⚙️"], "premium_enabled":True, "style":"primary", "callback_data":"a_backup_menu", "url":None, "position":7, "enabled":True},
    "ui_a_restore": {"label":"Restore", "normal_emoji":"♻️", "premium_emoji_id":EMOJI["✅"], "premium_enabled":True, "style":"danger", "callback_data":"a_restore", "url":None, "position":8, "enabled":True},
    "ui_a_dbhealth": {"label":"Database Health", "normal_emoji":"🩺", "premium_emoji_id":EMOJI["📊"], "premium_enabled":True, "style":"primary", "callback_data":"a_dbhealth", "url":None, "position":9, "enabled":True},
    "ui_a_health": {"label":"Bot Health", "normal_emoji":"❤️", "premium_emoji_id":EMOJI["🌟"], "premium_enabled":True, "style":"success", "callback_data":"a_health", "url":None, "position":10, "enabled":True},
    "ui_a_settings": {"label":"Settings", "normal_emoji":"⚙️", "premium_emoji_id":EMOJI["⚙️"], "premium_enabled":True, "style":"primary", "callback_data":"a_settings", "url":None, "position":11, "enabled":True},
    "ui_a_premium_test": {"label":"Premium Button Test", "normal_emoji":"🧪", "premium_emoji_id":EMOJI["🌟"], "premium_enabled":True, "style":"success", "callback_data":"a_premium_test", "url":None, "position":12, "enabled":True},
    "ui_a_errors": {"label":"Error Log", "normal_emoji":"📜", "premium_emoji_id":EMOJI["📝"], "premium_enabled":True, "style":"primary", "callback_data":"a_errors", "url":None, "position":13, "enabled":True},
    "ui_a_close": {"label":"Close", "normal_emoji":"", "premium_emoji_id":EMOJI["❌"], "premium_enabled":True, "style":"danger", "callback_data":"a_close", "url":None, "position":14, "enabled":True},
    # Force-join controls. ``{name}`` is replaced with the configured channel name,
    # so one admin template controls every channel button.
    "ui_join_channel": {"label":"{name}", "normal_emoji":"", "premium_emoji_id":EMOJI["📣"], "premium_enabled":True, "style":"primary", "callback_data":"join_channel", "url":None, "position":16, "enabled":True},
    "ui_join_check": {"label":"Joined", "normal_emoji":"", "premium_emoji_id":EMOJI["✅"], "premium_enabled":True, "style":"success", "callback_data":"check_joined", "url":None, "position":17, "enabled":True},
    # Global Back button configuration. Every Back button in the bot uses this key,
    # so its name, premium custom emoji, style and enabled state can
    # be managed from the same Admin > Buttons screen. Callback data is overridden
    # per destination and therefore remains unchanged.
    "ui_back": {"label":"Back", "normal_emoji":"🔙", "premium_emoji_id":EMOJI["📌"], "premium_enabled":True, "style":"primary", "callback_data":"a_back", "url":None, "position":15, "enabled":True},
}
BUTTON_STYLES = ("primary", "success", "danger")
BUTTON_CONFIG_PREFIX = "button_cfg_"


def _default_config(key):
    d=BUTTON_DEFAULTS.get(key)
    return dict(d) if d else None


def _strip_known_leading_emoji(text):
    v=str(text or "").strip()
    for emoji in sorted(EMOJI.keys(), key=len, reverse=True):
        if v.startswith(emoji):
            return v[len(emoji):].lstrip()
    return v


def _config_to_json(cfg):
    import json
    return json.dumps(cfg,ensure_ascii=False,separators=(",",":"))


def _config_from_json(raw):
    import json
    try:
        v=json.loads(raw)
        return v if isinstance(v,dict) else None
    except Exception:
        return None


def migrate_button_configs(conn=None):
    """Create idempotent v5 button config records and migrate legacy settings."""
    own=conn is None
    if own:
        conn=sqlite3.connect(DB_PATH,timeout=30,check_same_thread=False)
    try:
        for key,default in BUTTON_DEFAULTS.items():
            raw=conn.execute("SELECT value FROM settings WHERE key=?",(BUTTON_CONFIG_PREFIX+key,)).fetchone()
            if raw:
                continue
            cfg=dict(default)
            if key in ("btn1","btn2","btn3"):
                idx=key[-1]
                legacy_label={"btn1":BTN1,"btn2":BTN2,"btn3":BTN3}[key]
                cfg["label"]=_strip_known_leading_emoji(legacy_label)
                cfg["style"]=conn.execute("SELECT value FROM settings WHERE key=?",("button_style_"+key,)).fetchone()
                cfg["style"]=cfg["style"][0] if cfg["style"] else default["style"]
                eid=conn.execute("SELECT value FROM settings WHERE key=?",("button_emoji_"+key,)).fetchone()
                enabled=conn.execute("SELECT value FROM settings WHERE key=?",("button_emoji_enabled_"+key,)).fetchone()
                cfg["premium_emoji_id"]=eid[0] if eid and str(eid[0]).isdigit() else default["premium_emoji_id"]
                cfg["premium_enabled"]=(enabled[0] == "1") if enabled else default["premium_enabled"]
            if cfg.get("style") not in BUTTON_STYLES: cfg["style"]=default["style"]
            conn.execute("INSERT OR IGNORE INTO settings(key,value) VALUES(?,?)",(BUTTON_CONFIG_PREFIX+key,_config_to_json(cfg)))
        if own: conn.commit()
    finally:
        if own: conn.close()


def get_button_config(key):
    default=_default_config(key)
    if not default: return None
    raw=gset(BUTTON_CONFIG_PREFIX+key,"")
    cfg=_config_from_json(raw) if raw else None
    if not cfg:
        migrate_button_configs(); raw=gset(BUTTON_CONFIG_PREFIX+key,""); cfg=_config_from_json(raw) if raw else None
    cfg=cfg or dict(default)
    merged=dict(default);merged.update(cfg)
    merged["label"]=_strip_known_leading_emoji(merged.get("label",default["label"])) or default["label"]
    merged["normal_emoji"]=str(merged.get("normal_emoji",default["normal_emoji"]) or "")
    pe=str(merged.get("premium_emoji_id","") or "")
    merged["premium_emoji_id"]=pe if pe.isdigit() else ""
    # Normal Unicode button icons are intentionally disabled.
    merged["normal_emoji"]=""
    merged["premium_enabled"]=bool(merged.get("premium_enabled",default["premium_enabled"]))
    merged["style"]=merged.get("style") if merged.get("style") in BUTTON_STYLES else default["style"]
    merged["position"]=int(merged.get("position",default["position"]) or default["position"])
    merged["enabled"]=bool(merged.get("enabled",default["enabled"]))
    merged["callback_data"]=default["callback_data"]
    merged["url"]=default.get("url")
    return merged


def save_button_config(key, **changes):
    cfg=get_button_config(key)
    if not cfg: raise KeyError(key)
    for field,value in changes.items():
        if field not in cfg or field in {"label","normal_emoji","premium_emoji_id","premium_enabled","style","position","enabled"}:
            cfg[field]=value
    cfg["label"]=_clean_visible_label(cfg.get("label",""))
    if not safe_button_text(cfg["label"]): raise ValueError("Button name must contain visible text.")
    if cfg.get("style") not in BUTTON_STYLES: raise ValueError("Invalid button style.")
    cfg["premium_emoji_id"]="" if str(cfg.get("premium_emoji_id","")).strip().lower()=="clear" else str(cfg.get("premium_emoji_id","")).strip()
    if cfg["premium_emoji_id"] and not cfg["premium_emoji_id"].isdigit(): raise ValueError("Premium Emoji ID must be numeric.")
    cfg["normal_emoji"]=""
    cfg["premium_enabled"]=True
    cfg["position"]=max(1,int(cfg.get("position",1)))
    cfg["enabled"]=bool(cfg.get("enabled",True))
    with db() as c: c.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)",(BUTTON_CONFIG_PREFIX+key,_config_to_json(cfg)))
    # Keep legacy public settings in sync for old integrations/backups/admin tools.
    if key in ("btn1","btn2","btn3"):
        with db() as c:
            c.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)",("button_style_"+key,cfg["style"]))
            c.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)",("button_emoji_"+key,cfg["premium_emoji_id"]))
            c.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)",("button_emoji_enabled_"+key,"1" if cfg["premium_enabled"] and cfg["premium_emoji_id"] else "0"))
    return cfg


def reset_button_config(key):
    cfg=_default_config(key)
    if not cfg: raise KeyError(key)
    return save_button_config(key,**cfg)


def reset_all_button_configs():
    for key in BUTTON_DEFAULTS: reset_button_config(key)


def public_button_keys():
    return [k for k in BUTTON_DEFAULTS if not k.startswith("ui_") and get_button_config(k).get("enabled")]


def admin_button_keys():
    # Only real Admin Dashboard controls belong on the dashboard.
    # Force-join controls and the global Back control are rendered only in
    # their own contexts; exposing them here creates dead buttons such as
    # "{name}" / "Joined" on the admin home screen.
    return sorted((k for k in BUTTON_DEFAULTS if k.startswith("ui_a_") and get_button_config(k).get("enabled")),key=lambda k:get_button_config(k)["position"])


def premium_system_enabled():
    # Premium custom emoji mode is intentionally locked ON for button rendering.
    # This prevents duplicate/normal Unicode button icons and keeps the UI consistent.
    return True


def _strip_leading_button_emoji(text):
    """Remove visible Unicode emoji from the beginning of button labels.

    Buttons in this bot use Telegram custom emoji IDs as their icon, so a second
    Unicode emoji would otherwise produce the duplicate-icon look shown in the
    reported UI. This strips common emoji code-point ranges without changing the
    rest of the label.
    """
    import re
    v=str(text or "").strip()
    pattern=(r"^[\s\u200d\ufe0f\u20e3]*"
             r"(?:[\U0001F1E6-\U0001FAFF]|[\u2600-\u27BF]|[\u2300-\u23FF])"
             r"(?:[\ufe0f\u200d\u20e3\U0001F3FB-\U0001F3FF]|\u2640\ufe0f|\u2642\ufe0f)*")
    previous=None
    while previous != v:
        previous=v
        v=re.sub(pattern,"",v).lstrip()
    return v

def _remove_invisible_chars(value):
    """Remove characters that do not provide visible button text."""
    import unicodedata
    s=str(value or "")
    invisible={"\u200b","\u200c","\u200d","\u2060","\ufeff","\ufe0f"}
    return "".join(ch for ch in s if ch not in invisible and unicodedata.category(ch) not in {"Cf","Cc"} or ch in {"\n","\t","\r"})

def safe_button_text(text):
    """Return Telegram-safe visible button text, or an empty string if invalid."""
    value=_remove_invisible_chars(text).strip()
    value=_strip_leading_button_emoji(value).strip()
    value=_remove_invisible_chars(value).strip()
    return value

def _button_is_valid(button):
    return bool(button is not None and safe_button_text(getattr(button,"text","")))

def safe_markup(rows):
    """Build an InlineKeyboardMarkup after removing every invalid button/row."""
    if rows is None:
        return TelegramMarkup([])
    valid_rows=[]
    for row in rows:
        if row is None:
            continue
        valid=[]
        for button in row:
            if _button_is_valid(button):
                valid.append(button)
        if valid:
            valid_rows.append(valid)
    return TelegramMarkup(valid_rows)

def _build_button(text,callback_data=None,url=None,style=None,emoji_id=None):
    # Low-level button builder: Unicode emoji is removed from the label and the
    # visible icon is carried by Telegram's premium/custom emoji field.
    final_text=safe_button_text(text)
    if not final_text:
        logger.warning("Skipping invalid inline button with empty visible text: %r", text)
        return None
    kw={"text":final_text}
    if callback_data is not None: kw["callback_data"]=str(callback_data)
    if url is not None: kw["url"]=str(url)
    if style in BUTTON_STYLES: kw["style"]=style
    if emoji_id and premium_system_enabled():
        kw["icon_custom_emoji_id"]=str(emoji_id)
    try: return InlineKeyboardButton(**kw)
    except (TypeError,ValueError):
        kw.pop("style",None);kw.pop("icon_custom_emoji_id",None)
        try: return InlineKeyboardButton(**kw)
        except (TypeError,ValueError):
            logger.exception("Unable to construct safe inline button")
            return None


def ib(text,callback_data=None,url=None,style=None,emoji_id=None):
    return _build_button(text,callback_data=callback_data,url=url,style=style,emoji_id=emoji_id)


def render_button(key,callback_data=None,url=None):
    cfg=get_button_config(key)
    if not cfg or not cfg.get("enabled"): return None
    cb=cfg["callback_data"] if callback_data is None else callback_data
    target_url=cfg.get("url") if url is None else url
    # Buttons are premium-only. If an ID is missing/invalid, the builder safely
    # renders the label without a visible Unicode emoji rather than reintroducing a
    # duplicate normal emoji.
    text=cfg["label"]
    return _build_button(text,callback_data=cb,url=target_url,style=cfg.get("style"),emoji_id=cfg.get("premium_emoji_id"))


def render_button_markup(key,callback_data=None,url=None):
    b=render_button(key,callback_data=callback_data,url=url)
    return safe_markup([[b]]) if b else safe_markup([])


def bstyle(k):
    cfg=get_button_config(k)
    return cfg["style"] if cfg else "primary"


def bemoji(k):
    cfg=get_button_config(k)
    return cfg.get("premium_emoji_id") if cfg and cfg.get("premium_enabled") and cfg.get("premium_emoji_id") else None


def without_premium_markup(markup):
    if not markup: return markup
    rows=[]
    for row in markup.inline_keyboard:
        nr=[]
        for btn in row:
            text=str(btn.text or "")
            eid=getattr(btn,"icon_custom_emoji_id",None)
            if eid:
                reverse=next((em for em,known in EMOJI.items() if str(known)==str(eid)),None)
                if reverse and text.startswith(reverse): text=_strip_known_leading_emoji(text)
                elif text and reverse is None: text="" + text
            nr.append(_build_button(text,callback_data=btn.callback_data,url=btn.url,style=btn.style,emoji_id=None))
        rows.append(nr)
    return safe_markup(rows)


def _legacy_names(k):
    cfg=get_button_config(k);return cfg["label"] if cfg else k

def referral_count(uid):
    return scalar("SELECT COUNT(*) FROM referrals WHERE referrer_id=?",(uid,),0)

def referral_link(bot_username, uid):
    return f"https://t.me/{bot_username}?start={uid}"

async def referral_text(bot, uid):
    me=await bot.get_me()
    count=referral_count(uid)
    target=max(1,int(gset("referral_target","1") or "1"))
    reward=gset("referral_reward","1")
    needed=max(0,target-count)
    link=referral_link(me.username or "",uid)
    return (
        "🤩<b>ᴍʏ ʀᴇꜰᴇʀʀᴀʟ ʟɪɴᴋ</b>\n\n"
        "━━━━━━━━━━━━━━━━━━━━━\n\n"
        f"💎 <b>ᴘᴇʀ ʀᴇꜰᴇʀʀ :</b> {esc(reward)}\n\n"
        f"👥 <b>ʀᴇꜰᴇʀʀᴀʟs :</b> {count}\n\n"
        f"🎯 <b>ᴛᴀʀɢᴇᴛ :</b> {target}\n\n"
        f"⏳ <b>ꜱᴛɪʟʟ ɴᴇᴇᴅᴇᴅ :</b> {needed}\n\n"
        "━━━━━━━━━━━━━━━━━━━━━\n\n"
        f"🔑 <b>ɪɴᴠɪᴛᴀᴛɪᴏɴ ᴄᴏᴅᴇ :</b> <code>{uid}</code>\n\n"
        f"<code>{esc(link)}</code>\n\n"
        "📨<b>ꜱʜᴀʀᴇ ᴡɪᴛʜ ꜰʀɪᴇɴᴅs.</b>"
    )

def referral_kb(link):
    share_url=("https://t.me/share/url?url="+quote(link,safe=""))+"&text="+quote("Join this bot using my referral link!",safe="")
    return safe_markup([[ib("📤 Share Referral Link",url=share_url,style="success",emoji_id=EMOJI["📣"])],[back_button("back_main")]] )

async def show_referral(update,ctx):
    uid=update.effective_user.id
    try:
        me=await ctx.bot.get_me()
        text=await referral_text(ctx.bot,uid)
        kb=referral_kb(referral_link(me.username or "",uid))
        if update.callback_query:
            q=update.callback_query
            await q.edit_message_text(text,reply_markup=kb,parse_mode=ParseMode.HTML)
        else:
            await update.message.reply_text(text,reply_markup=kb,parse_mode=ParseMode.HTML)
    except TelegramError as e:
        logger.error("Referral UI failed: %s",e)

def process_referral(new_user_id, args):
    if not args: return False
    code=str(args[0]).strip()
    if not code.isdigit(): return False
    referrer_id=int(code)
    if referrer_id==new_user_id: return False
    if not scalar("SELECT 1 FROM users WHERE user_id=?",(referrer_id,),0): return False
    try:
        with db() as c:
            c.execute("INSERT INTO referrals(user_id,referrer_id,created_at) VALUES(?,?,?)",(new_user_id,referrer_id,datetime.now().isoformat()))
        return True
    except sqlite3.IntegrityError:
        return False

def main_kb():
    keys=public_button_keys()
    buttons=[render_button(k) for k in keys]
    buttons=[b for b in buttons if b]
    rows=[]
    for i in range(0,len(buttons),2): rows.append(buttons[i:i+2])
    return safe_markup(rows)

def back_button(callback_data="a_back"):
    """Build the globally configurable Back button with a per-screen callback."""
    return render_button("ui_back", callback_data=callback_data) or ib("🔙 Back", callback_data, style="primary", emoji_id=EMOJI["📌"])

def back_kb(cb="a_back"):
    return safe_markup([[back_button(cb)]])

def join_kb(rows,joined):
    """Build force-join buttons two-per-row, preserving channel order."""
    out=[]
    cfg=get_button_config("ui_join_channel") or BUTTON_DEFAULTS["ui_join_channel"]
    template=str(cfg.get("label") or "{name}")
    icon=cfg.get("premium_emoji_id") or gset("join_channel_premium_emoji_id",EMOJI["📣"])
    style=cfg.get("style","primary")
    pending=[]
    for r in rows:
        if not r[6] or r[1] in joined:
            continue
        label=template.replace("{name}",str(r[2]))
        if not label.strip() or label.strip()=="{name}":
            label=str(r[2])
        pending.append(ib(label,url=r[3],style=style,emoji_id=icon))
    for i in range(0,len(pending),2):
        out.append(pending[i:i+2])
    check=render_button("ui_join_check",callback_data="check_joined")
    if check:
        out.append([check])
    return safe_markup(out)

def get_force_join_message():
    return str(gset("force_join_message","") or "").strip()

async def render_force_join(bot,chat_id,user_id=None,rows=None,verification=None,existing_message=None):
    """The single authoritative Force Join UI renderer."""
    rows=channels(False) if rows is None else [r for r in rows if r[6]]
    if user_id is None:
        user_id=chat_id
    verification=await verify_required_channels(bot,user_id,rows)
    remaining=verification.get("remaining",[])
    text=get_force_join_message()
    kb=join_kb(remaining,set(verification.get("joined",set())))
    photo=str(gset("welcome_photo","") or "").strip()
    photo_enabled=gset("welcome_photo_enabled","1")=="1"

    async def do_render(markup):
        if existing_message is not None:
            if getattr(existing_message,"photo",None):
                return await bot.edit_message_caption(
                    chat_id=chat_id,message_id=existing_message.message_id,
                    caption=text or None,reply_markup=markup,parse_mode=ParseMode.HTML)
            if text:
                return await bot.edit_message_text(
                    chat_id=chat_id,message_id=existing_message.message_id,
                    text=text,reply_markup=markup,parse_mode=ParseMode.HTML)
            raise TelegramError("Cannot edit an existing text message to empty content.")
        if photo and photo_enabled:
            kwargs={"chat_id":chat_id,"photo":photo,"reply_markup":markup}
            if text: kwargs.update(caption=text,parse_mode=ParseMode.HTML)
            return await bot.send_photo(**kwargs)
        if not text:
            raise TelegramError(
                "Force Join message is empty and no photo is configured; "
                "Telegram does not support a keyboard-only message.")
        return await bot.send_message(
            chat_id=chat_id,text=text,reply_markup=markup,parse_mode=ParseMode.HTML)

    try:
        return await do_render(kb)
    except TelegramError as e:
        msg=str(e).lower()
        if "message is not modified" in msg or "message not modified" in msg:
            logger.info("ForceJoin render unchanged user=%s",user_id)
            return existing_message
        if any(t in msg for t in ("custom emoji","icon_custom_emoji_id","custom_emoji_id")):
            logger.warning("ForceJoin custom emoji rejected; retrying without premium icons: %s",e)
            try:return await do_render(without_premium_markup(kb))
            except TelegramError as e2:
                if existing_message is not None:
                    logger.warning("ForceJoin edit failed after custom emoji fallback; sending fresh UI user=%s: %s",user_id,e2)
                    return await render_force_join(bot,chat_id,user_id,rows=rows,verification=verification,existing_message=None)
                raise
        if existing_message is not None:
            logger.warning("ForceJoin existing message render failed; sending fresh UI user=%s: %s",user_id,e)
            return await render_force_join(bot,chat_id,user_id,rows=rows,verification=verification,existing_message=None)
        raise

async def start(update,ctx):
    u=update.effective_user
    if not u:return
    is_new=add_user(u)
    if is_new and ctx.args: process_referral(u.id,ctx.args)
    if user_status(u.id)=="blocked":
        return await update.message.reply_text("🚫 You are blocked from using this bot.")
    if gset("maintenance_mode","0")=="1" and not is_admin(u.id):
        return await update.message.reply_text("🛠 Bot is under maintenance.")

    rows=channels(False)
    if not rows or is_admin(u.id) or gset("force_join_enabled","1")!="1":
        ctx.user_data.pop("force_join_message_id",None)
        ctx.user_data.pop("force_join_message_photo",None)
        post=str(gset("postjoin","") or "").strip()
        return await update.message.reply_text(post or " ",reply_markup=main_kb(),parse_mode=ParseMode.HTML)

    verification=await verify_required_channels(ctx.bot,u.id,rows)
    if verification["all_verified"]:
        ctx.user_data.pop("force_join_message_id",None)
        ctx.user_data.pop("force_join_message_photo",None)
        post=str(gset("postjoin","") or "").strip()
        return await update.message.reply_text(post or " ",reply_markup=main_kb(),parse_mode=ParseMode.HTML)

    old_id=ctx.user_data.get("force_join_message_id")
    if old_id:
        try:
            await render_force_join(
                ctx.bot,u.id,u.id,rows=rows,verification=verification,
                existing_message=SimpleNamespace(
                    message_id=old_id,
                    photo=bool(ctx.user_data.get("force_join_message_photo",False))
                )
            )
            return
        except TelegramError:
            ctx.user_data.pop("force_join_message_id",None)
    try:
        m=await render_force_join(ctx.bot,u.id,u.id,rows=rows,verification=verification)
        if m and getattr(m,"message_id",None):
            ctx.user_data["force_join_message_id"]=m.message_id
            ctx.user_data["force_join_message_photo"]=bool(getattr(m,"photo",None))
    except TelegramError as e:
        logger.error("ForceJoin send failed user=%s: %s",u.id,e)


async def cb_check(update,ctx):
    q=update.callback_query;uid=q.from_user.id
    if user_status(uid)=="blocked":
        return await q.answer("🚫 You are blocked.",show_alert=True)

    rows=channels(False)
    verification=await verify_required_channels(ctx.bot,uid,rows)
    if verification["all_verified"]:
        await q.answer("✅ Verified")
        ctx.user_data.pop("force_join_message_id",None)
        post=str(gset("postjoin","") or "").strip();visible=post or " "
        try:
            if getattr(q.message,"photo",None):
                await q.edit_message_caption(caption=post or None,reply_markup=main_kb(),parse_mode=ParseMode.HTML)
            else:
                await q.edit_message_text(visible,reply_markup=main_kb(),parse_mode=ParseMode.HTML)
        except TelegramError:
            await ctx.bot.send_message(q.message.chat_id,visible,reply_markup=main_kb(),parse_mode=ParseMode.HTML)
        return

    await q.answer("Please join the remaining required channel(s) and press Joined again.",show_alert=True)
    try:
        await render_force_join(ctx.bot,q.message.chat_id,uid,rows=rows,
                                verification=verification,existing_message=q.message)
        ctx.user_data["force_join_message_id"]=q.message.message_id
        ctx.user_data["force_join_message_photo"]=bool(getattr(q.message,"photo",None))
    except TelegramError as e:
        logger.warning("ForceJoin re-render failed user=%s: %s",uid,e)

async def cb_btn(update,ctx):
    q=update.callback_query
    if user_status(q.from_user.id)=="blocked":return await q.answer("🚫 You are blocked.",show_alert=True)
    await q.answer()
    if q.data=="btn3":
        return await show_referral(update,ctx)
    k={"btn1":"btn1_msg","btn2":"btn2_msg"}.get(q.data)
    if not k:return
    try:await q.edit_message_text(gset(k),reply_markup=back_kb("back_main"),parse_mode=ParseMode.HTML)
    except TelegramError:await ctx.bot.send_message(q.message.chat_id,gset(k),reply_markup=back_kb("back_main"),parse_mode=ParseMode.HTML)
async def cb_ref_share(update,ctx):
    q=update.callback_query
    await q.answer()
    try:
        me=await ctx.bot.get_me()
        link=referral_link(me.username or "",q.from_user.id)
        await q.message.reply_text(f"📨 <b>Share this referral link:</b>\n\n<code>{esc(link)}</code>",parse_mode=ParseMode.HTML)
    except TelegramError as e:
        logger.warning("Referral share failed: %s",e)

async def cb_back(update,ctx):
    q=update.callback_query;await q.answer()
    try:await q.edit_message_text(gset("postjoin"),reply_markup=main_kb(),parse_mode=ParseMode.HTML)
    except TelegramError:await ctx.bot.send_message(q.message.chat_id,gset("postjoin"),reply_markup=main_kb(),parse_mode=ParseMode.HTML)
async def join_request(update,ctx):
    r=update.chat_join_request
    if r:
        uid = r.from_user.id
        cid = r.chat.id
        record_req(uid, cid)

        try:
            await r.approve()
        except telegram.error.TelegramError:
            pass

        rows = channels(False)
        verification = await verify_required_channels(ctx.bot, uid, rows)
        if verification["all_verified"]:
            post = str(gset("postjoin", "") or "").strip()
            try:
                await ctx.bot.send_message(uid, post or " ", reply_markup=main_kb(), parse_mode=telegram.constants.ParseMode.HTML)
            except telegram.error.TelegramError:
                pass

async def chat_member_update(update,ctx):
    cmu=update.chat_member
    if not cmu: return
    try:
        uid=cmu.new_chat_member.user.id
        cid=str(cmu.chat.id)
        new_status=str(getattr(cmu.new_chat_member,"status","") or "").lower()

        if new_status in ("member","administrator","creator","restricted"):
            mark_req(uid,cid)

            rows = channels(False)
            verification = await verify_required_channels(ctx.bot, uid, rows)
            if verification["all_verified"]:
                post = str(gset("postjoin", "") or "").strip()
                try:
                    await ctx.bot.send_message(uid, post or " ", reply_markup=main_kb(), parse_mode=telegram.constants.ParseMode.HTML)
                except telegram.error.TelegramError:
                    pass

        elif new_status in ("left","kicked","banned"):
            with db() as c:
                c.execute("UPDATE join_requests SET status='pending' WHERE user_id=? AND channel_id=? AND status='verified'",(uid,cid))
    except Exception:
        pass

def dash():
    now=datetime.now();today=now.date().isoformat();week=(now-timedelta(days=now.weekday())).date().isoformat()
    nt=scalar("SELECT COUNT(*) FROM users WHERE substr(joined_at,1,10)=?",(today,),0);nw=scalar("SELECT COUNT(*) FROM users WHERE substr(joined_at,1,10)>=?",(week,),0)
    up=int(time.monotonic()-STARTED_AT);sz=Path(DB_PATH).stat().st_size if Path(DB_PATH).exists() else 0
    return ("╔═━━━✦ 🤖 <b>ADVANCED ADMIN DASHBOARD</b> ✦━━━═╗\n\n"
            f"👥 Total Users: <b>{scalar('SELECT COUNT(*) FROM users')}</b>\n🆕 New Today: <b>{nt}</b>\n📅 New This Week: <b>{nw}</b>\n"
            f"📢 Total Channels: <b>{len(channels(True))}</b>\n📨 Active Join Requests: <b>{scalar('SELECT COUNT(*) FROM join_requests WHERE status=\'active\'')}</b>\n"
            f"📣 Broadcasts: <b>{scalar('SELECT COUNT(*) FROM broadcasts')}</b> | Sent <b>{scalar('SELECT COALESCE(SUM(sent),0) FROM broadcasts')}</b> | Failed <b>{scalar('SELECT COALESCE(SUM(failed),0) FROM broadcasts')}</b>\n"
            f"⏱ Uptime: <b>{up//86400}d {(up%86400)//3600}h {(up%3600)//60}m</b>\n💾 DB Size: <b>{sz/1024:.1f} KB</b>\n"
            f"🗄 Last Backup: <b>{esc(gset('last_backup','—'))}</b>\n♻️ Last Restore: <b>{esc(gset('last_restore','—'))}</b>\n🟢 Bot Status: <b>ONLINE</b>\n"
            f"🧩 Version: <code>{BOT_VERSION}</code>\n╚═━━━━━━━━━━━━━━━━━━━━━━━━═╝")

def admin_kb():
    items=[]
    for key in admin_button_keys():
        b=render_button(key)
        if b: items.append(b)
    rows=[]
    for i in range(0,len(items),2): rows.append(items[i:i+2])
    return safe_markup(rows)

async def admin_cmd(update,ctx):
    if not is_admin(update.effective_user.id):return await update.message.reply_text("❌ Not authorized!")
    await update.message.reply_text(dash(),reply_markup=admin_kb(),parse_mode=ParseMode.HTML)

async def dkboss_cmd(update,ctx):
    if not is_owner(update.effective_user.id):return await update.message.reply_text("❌ DK BOSS access denied!")
    await update.message.reply_text(
        "👑 <b>DK BOSS OWNER PANEL</b>\n\n" + dash(),
        reply_markup=admin_kb(), parse_mode=ParseMode.HTML
    )

def ch_kb():
    rows=[]
    for r in channels(True):
        cid,name,en=r[0],r[2],r[6]
        channel_label=_clean_visible_label(name) or f"Channel {str(r[1]).strip() or cid}"
        edit_label="Edit "+channel_label[:12]
        rows += [
            [ib(edit_label,f"a_editc_{cid}",style="primary",emoji_id=EMOJI["📝"]),
             ib("Left",f"a_left_{cid}",style="primary",emoji_id=EMOJI["📌"]),
             ib("Right",f"a_right_{cid}",style="primary",emoji_id=EMOJI["📌"])],
            [ib("Enable" if not en else "Disable",f"a_togglec_{cid}",style="success" if not en else "danger",emoji_id=EMOJI["✅"] if not en else EMOJI["❌"]),
             ib("Test",f"a_testc_{cid}",style="success",emoji_id=EMOJI["🌟"]),
             ib("Delete",f"a_delc_{cid}",style="danger",emoji_id=EMOJI["❌"])]
        ]
    rows += [[ib("Add Channel","a_addch",style="success",emoji_id=EMOJI["➕"])],[back_button("a_back")]]
    return safe_markup(rows)

async def show_channels(q):
    txt="📢 <b>CHANNEL MANAGEMENT</b>\n\n"
    for i,r in enumerate(channels(True),1):txt+=f"{i}. {'🟢' if r[6] else '🔴'} <b>{esc(r[2])}</b>\n   ID: <code>{esc(r[1])}</code>\n   Link: {esc(r[3])}\n"
    await q.edit_message_text(txt if len(channels(True)) else txt+"No channels configured.",reply_markup=ch_kb(),parse_mode=ParseMode.HTML)

def msg_kb():
    return safe_markup([
        [ib("📢 Top Message","a_top",style="primary",emoji_id=EMOJI["📣"])],
        [ib("👋 Welcome Message","a_welcome",style="primary",emoji_id=EMOJI["💬"])],
        [ib("🖼 Welcome Photo","a_welcome_photo",style="success",emoji_id=EMOJI["🖼️"])],
        [ib("📝 Force Join Message","a_forcejoin_message",style="primary",emoji_id=EMOJI["📝"])],
        [ib("🎉 Post-Join Message","a_postjoin",style="success",emoji_id=EMOJI["🌟"])],
        [ib("✉️ "+_legacy_names("btn1"),"a_btn1",style="primary",emoji_id=EMOJI["🎯"])],
        [ib("✉️ "+_legacy_names("btn2"),"a_btn2",style="success",emoji_id=EMOJI["📊"])],
        [ib("✉️ "+_legacy_names("btn3"),"a_btn3",style="primary",emoji_id=EMOJI["🤝"])],
        [back_button("a_back")]
    ])

def button_config_text(key):
    cfg=get_button_config(key) or {}
    return (f"<b>{esc(cfg.get('label',''))}</b>\n"
            f"Name: <code>{esc(cfg.get('label',''))}</code>\n"
            f"Premium Emoji: <code>{esc(cfg.get('premium_emoji_id','') or 'None')}</code>\n"
            f"Premium Emoji Mode: <b>ON</b>\n"
            f"Style: <b>{esc(cfg.get('style','primary'))}</b>\n"
            f"Position: <b>{cfg.get('position',1)}</b>\n"
            f"Enabled: <b>{'YES' if cfg.get('enabled') else 'NO'}</b>")

def btn_kb():
    rows=[[ib("Public Buttons","a_public_buttons",style="primary",emoji_id=EMOJI["🎯"]),
           ib("Admin Buttons","a_admin_buttons",style="success",emoji_id=EMOJI["⚙️"])],
          [ib("Join / Verify Buttons","a_joinbuttons",style="primary",emoji_id=EMOJI["📣"])],
          [ib("Reset All Buttons","a_reset_all",style="danger",emoji_id=EMOJI["❌"])],
          [ib("Premium Button Test","a_premium_test",style="success",emoji_id=EMOJI["🌟"])],
          [back_button("a_back")]]
    return safe_markup(rows)

def button_list_kb(prefix):
    keys=public_button_keys() if prefix=="public" else admin_button_keys()
    rows=[]
    for key in keys:
        cfg=get_button_config(key)
        rows.append([ib(cfg["label"][:28],f"a_editbutton_{key}",style=cfg["style"],emoji_id=cfg.get("premium_emoji_id"))])
    rows.append([ib("➕ Show Disabled","a_show_disabled_"+prefix,style="primary",emoji_id=EMOJI["📌"])])
    rows.append([back_button("a_buttons")])
    return safe_markup(rows)

def button_editor_kb(key):
    cfg=get_button_config(key)
    return safe_markup([
        [ib("Name","a_btnname_"+key,style="primary",emoji_id=EMOJI["📝"])],
        [ib("Premium Emoji","a_btnpremium_"+key,style="success",emoji_id=EMOJI["👑"])],
        [ib("Style: "+cfg.get("style","primary"),"a_style_"+key,style=cfg.get("style","primary"),emoji_id=EMOJI["🌟"])],
        [ib("Up","a_moveup_"+key,style="primary",emoji_id=EMOJI["📌"]),ib("Down","a_movedown_"+key,style="primary",emoji_id=EMOJI["📌"])],
        [ib("Enabled" if cfg.get("enabled") else "Disabled","a_enable_"+key,style="success" if cfg.get("enabled") else "danger",emoji_id=EMOJI["✅"] if cfg.get("enabled") else EMOJI["❌"])],
        [ib("Preview","a_preview_"+key,style="primary",emoji_id=EMOJI["📌"]),ib("Test","a_testbutton_"+key,style="success",emoji_id=EMOJI["🌟"])],
        [ib("Reset","a_reset_"+key,style="danger",emoji_id=EMOJI["❌"])],
        [back_button("a_public_buttons" if not key.startswith("ui_") else "a_admin_buttons")]
    ])

def render_button_editor_text(key):
    cfg=get_button_config(key)
    return "🎨 <b>BUTTON CONFIGURATION</b>\n\n"+button_config_text(key) + "\n\n<b>Current Preview</b>"

def settings_kb():
    def t(k,n):
        on=gset(k,"0")=="1";return ib(("🟢 " if on else "🔴 ")+n+": "+("ON" if on else "OFF"),"a_toggle_"+k,style="success" if on else "danger",emoji_id=EMOJI["✅"] if on else EMOJI["❌"])
    return safe_markup([[t("maintenance_mode","Maintenance Mode")],[t("force_join_enabled","Force Join")],[t("welcome_photo_enabled","Welcome Photo")],[t("broadcast_enabled","Broadcast")],[t("auto_backup_enabled","Auto Backup")],[t("debug_logging","Debug Logging")],[ib("🕒 Auto Backup: "+gset("auto_backup_frequency","daily"),"a_autobackup",style="primary",emoji_id=EMOJI["🔔"])],[back_button("a_back")]] )

def health():
    up=int(time.monotonic()-STARTED_AT)
    return ("❤️ <b>BOT HEALTH</b>\n\n🟢 Online\n"
            f"Uptime: <b>{up//86400}d {(up%86400)//3600}h {(up%3600)//60}m</b>\n"
            f"Python: <code>{sys.version.split()[0]}</code>\nPTB: <code>{telegram.__version__}</code>\n"
            f"DB: <code>{esc(DB_PATH)}</code>\nLast Error: <code>{esc(LAST_ERROR or 'None')}</code>\n"
            f"Last Backup: <code>{esc(gset('last_backup','None'))}</code>\nLast Restore: <code>{esc(gset('last_restore','None'))}</code>")

def dbhealth():
    try:
        with db() as c:
            ok=c.execute("PRAGMA integrity_check").fetchone()[0];wal=c.execute("PRAGMA journal_mode").fetchone()[0]
            vals=[("Users","users"),("Channels","channels"),("Settings","settings"),("Join Requests","join_requests"),("Broadcast Records","broadcasts")]
            s=f"🩺 <b>DATABASE HEALTH</b>\n\nStatus: {'🟢 HEALTHY' if ok=='ok' else '🔴 CORRUPT'}\nWAL: <b>{wal}</b>\nSize: <b>{Path(DB_PATH).stat().st_size/1024:.1f} KB</b>\n"
            return s+"\n".join(f"{n}: <b>{c.execute('SELECT COUNT(*) FROM '+t).fetchone()[0]}</b>" for n,t in vals)
    except Exception as e:return "🔴 Database health check failed:\n<code>"+esc(e)+"</code>"

def safe_zip(z):
    for n in z.namelist():
        p=Path(n)
        if p.is_absolute() or ".." in p.parts:raise ValueError("Unsafe backup archive: path traversal detected.")

def migrate_database_file(path):
    """Bring a legacy SQLite backup forward without touching the live DB."""
    c=sqlite3.connect(path,timeout=30,check_same_thread=False)
    try:
        c.executescript("""
        CREATE TABLE IF NOT EXISTS users(user_id INTEGER PRIMARY KEY,first_name TEXT DEFAULT '',username TEXT DEFAULT '',joined_at TEXT NOT NULL,status TEXT NOT NULL DEFAULT 'active');
        CREATE TABLE IF NOT EXISTS channels(id INTEGER PRIMARY KEY AUTOINCREMENT,channel_id TEXT UNIQUE NOT NULL,channel_name TEXT NOT NULL,channel_link TEXT NOT NULL,position INTEGER DEFAULT 0,order_num INTEGER DEFAULT 0,enabled INTEGER NOT NULL DEFAULT 1);
        CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY,value TEXT);
        CREATE TABLE IF NOT EXISTS join_requests(user_id INTEGER NOT NULL,channel_id TEXT NOT NULL,requested_at TEXT,status TEXT DEFAULT 'active',PRIMARY KEY(user_id,channel_id));
        CREATE TABLE IF NOT EXISTS broadcast_msgs(bcast_id TEXT NOT NULL,user_id INTEGER NOT NULL,message_id INTEGER NOT NULL);
        CREATE TABLE IF NOT EXISTS broadcasts(bcast_id TEXT PRIMARY KEY,created_at TEXT,source_chat_id INTEGER,source_message_id INTEGER,kind TEXT,total INTEGER DEFAULT 0,sent INTEGER DEFAULT 0,failed INTEGER DEFAULT 0,cancelled INTEGER DEFAULT 0,status TEXT DEFAULT 'running',last_error TEXT DEFAULT '',button_url TEXT DEFAULT '',button_label TEXT DEFAULT '',button_style TEXT DEFAULT '');
        CREATE TABLE IF NOT EXISTS error_logs(id INTEGER PRIMARY KEY AUTOINCREMENT,created_at TEXT,level TEXT,message TEXT);
        CREATE TABLE IF NOT EXISTS referrals(referral_id INTEGER PRIMARY KEY AUTOINCREMENT,user_id INTEGER UNIQUE NOT NULL,referrer_id INTEGER NOT NULL,created_at TEXT NOT NULL);
        """)
        migrate_force_join_message_setting(c)
        migrate_force_join_legacy_state(c)
        for table,required in {
            "users":("username","status"),
            "channels":("enabled",),
            "join_requests":("requested_at","status"),
        }.items():
            cols={r[1] for r in c.execute("PRAGMA table_info("+table+")")}
            for col in required:
                if col in cols: continue
                if table=="users" and col=="username": c.execute("ALTER TABLE users ADD COLUMN username TEXT DEFAULT ''")
                elif table=="users" and col=="status": c.execute("ALTER TABLE users ADD COLUMN status TEXT NOT NULL DEFAULT 'active'")
                elif table=="channels" and col=="enabled": c.execute("ALTER TABLE channels ADD COLUMN enabled INTEGER NOT NULL DEFAULT 1")
                elif table=="join_requests" and col=="requested_at": c.execute("ALTER TABLE join_requests ADD COLUMN requested_at TEXT")
                elif table=="join_requests" and col=="status": c.execute("ALTER TABLE join_requests ADD COLUMN status TEXT DEFAULT 'active'")
        c.execute("UPDATE join_requests SET requested_at=COALESCE(requested_at,datetime('now'))")
        # Repair legacy labels/channel names before the restored DB is accepted.
        sanitize_database_values(c)
        c.commit()
    finally:
        c.close()

def _find_backup_db(z):
    """Locate the SQLite database inside current or legacy backup archives."""
    names=[n for n in z.namelist() if not n.endswith("/") and Path(n).name.lower() not in {"manifest.txt","backup_manifest.txt"}]
    if "bot2.db" in names:
        return "bot2.db"
    # Legacy backups may use bot.db, database.db, *.sqlite, etc. Identify the
    # database by its SQLite file signature rather than trusting the filename.
    for name in names:
        try:
            with z.open(name) as f:
                if f.read(16).startswith(b"SQLite format 3\x00"):
                    return name
        except Exception:
            continue
    raise ValueError("Backup archive does not contain a SQLite database.")
def validate_backup(path):
    try:
        with zipfile.ZipFile(path) as z:
            safe_zip(z)
            if z.testzip() is not None:
                raise ValueError("Backup archive contains a damaged file.")
            db_name=_find_backup_db(z)
            with tempfile.TemporaryDirectory() as td:
                p=Path(td)/"restore_check.db"
                with z.open(db_name) as src, p.open("wb") as dst:
                    shutil.copyfileobj(src,dst)
                migrate_database_file(p)
                validate_backup_from_db(p)
            return db_name
    except zipfile.BadZipFile as e:
        raise ValueError("Invalid backup ZIP file.") from e

def create_backup():
    """Create a consistent SQLite backup without touching Telegram polling.

    The backup is fully local: it does not call the Telegram API and must never
    start/stop the application or interfere with getUpdates polling.
    """
    ts=datetime.now().strftime("%Y%m%d_%H%M%S_%f");zip_path=BACKUP_DIR/f"bot_backup_{ts}.zip";tmp=BACKUP_DIR/f".{ts}.db";man=BACKUP_DIR/f".{ts}.txt"
    try:
        src=sqlite3.connect(DB_PATH, timeout=30)
        dst=sqlite3.connect(tmp, timeout=30)
        try:
            src.execute("PRAGMA busy_timeout=30000")
            dst.execute("PRAGMA busy_timeout=30000")
            with dst:src.backup(dst, pages=256, sleep=0.05)
        finally:
            src.close();dst.close()
        validate_backup_from_db(tmp)
        man.write_text(
            f"Telegram Bot Live-State Database Backup\n"
            f"Backup Date: {datetime.now().isoformat()}\n"
            f"Database Version: {DB_VERSION}\n"
            f"Bot Version: {BOT_VERSION}\n"
            f"Database Name: {Path(DB_PATH).name}\n"
            f"Snapshot: consistent SQLite backup of the live database state\n"
            f"Secrets: BOT_TOKEN is NOT included.\n",
            encoding="utf-8"
        )
        with zipfile.ZipFile(zip_path,"w",zipfile.ZIP_DEFLATED) as z:z.write(tmp,"bot2.db");z.write(man,"manifest.txt")
        sset("last_backup",datetime.now().isoformat());return zip_path
    finally:tmp.unlink(missing_ok=True);man.unlink(missing_ok=True)

def validate_backup_from_db(p):
    c=sqlite3.connect(p);ok=c.execute("PRAGMA integrity_check").fetchone()[0];tables={r[0] for r in c.execute("SELECT name FROM sqlite_master WHERE type='table'")};c.close()
    req={"users","channels","settings","join_requests","broadcast_msgs","broadcasts","error_logs","referrals"}
    if ok!="ok" or not req.issubset(tables):raise ValueError("Database integrity check failed.")

def restore_backup(path):
    """Safely restore a current or legacy SQLite backup.

    The uploaded archive is validated first. A current live-state safety backup
    is created before the swap. Legacy archives are accepted when their SQLite
    database is valid; init_db() then performs the normal schema migrations.
    """
    db_name=validate_backup(path)
    safety=create_backup()
    live=Path(DB_PATH);live.parent.mkdir(parents=True,exist_ok=True)
    previous=Path(str(live)+".restore_previous")
    try:
        with zipfile.ZipFile(path) as z,tempfile.TemporaryDirectory(dir=str(live.parent)) as td:
            restored=Path(td)/"restored.db"
            with z.open(db_name) as src, restored.open("wb") as dst:
                shutil.copyfileobj(src,dst)
            migrate_database_file(restored)
            validate_backup_from_db(restored)
            # Keep a byte-for-byte rollback copy until the new DB is initialized.
            if live.exists():
                shutil.copy2(live,previous)
            for sidecar in (Path(str(live)+"-wal"),Path(str(live)+"-shm")):
                sidecar.unlink(missing_ok=True)
            os.replace(restored,live)
        # Apply schema migrations to older backups and verify the resulting DB.
        init_db()
        validate_backup_from_db(live)
        sset("last_restore",datetime.now().isoformat())
        previous.unlink(missing_ok=True)
        return safety
    except Exception:
        # Roll back automatically if the restored DB cannot be initialized/validated.
        try:
            if previous.exists():
                for sidecar in (Path(str(live)+"-wal"),Path(str(live)+"-shm")):
                    sidecar.unlink(missing_ok=True)
                os.replace(previous,live)
                init_db()
        except Exception:
            logger.exception("Restore rollback failed")
        raise

async def premium_test(bot,chat,key="btn1"):
    cfg=get_button_config(key) or BUTTON_DEFAULTS["btn1"]
    b=render_button(key,callback_data="premium_button_test")
    if not b: b=ib(cfg["label"],"premium_button_test",style=cfg["style"],emoji_id=cfg.get("premium_emoji_id"))
    text=("🧪 <b>Premium Button Test</b>\n\n"
          f"Selected button: <b>{esc(cfg['label'])}</b>\n"
          f"Style: <code>{esc(cfg['style'])}</code>\n"
          f"Premium enabled: <code>{'ON' if cfg.get('premium_enabled') else 'OFF'}</code>\n"
          f"icon_custom_emoji_id: <code>{esc(cfg.get('premium_emoji_id') or 'None')}</code>\n"
          f"callback_data: <code>premium_button_test</code>")
    try:
        await bot.send_message(chat,text,reply_markup=safe_markup([[b]]),parse_mode=ParseMode.HTML);return True
    except TelegramError as e:
        if "custom emoji" in str(e).lower() or "icon_custom_emoji_id" in str(e).lower() or "rights" in str(e).lower():
            log_error("WARNING","Premium test fallback: "+str(e))
            try:
                fb=without_premium_markup(safe_markup([[b]]))
                await bot.send_message(chat,"Premium icon unavailable for this request.\n\nThe button label remains active without a Unicode emoji.",reply_markup=fb);return False
            except TelegramError:logger.exception("Premium test fallback failed")
        else: raise


def backup_list():return sorted(BACKUP_DIR.glob("*.zip"),key=lambda p:p.stat().st_mtime,reverse=True)
def cleanup_backups():
    try:n=max(1,int(gset("auto_backup_keep","7")))
    except ValueError:n=7
    for p in backup_list()[n:]:p.unlink(missing_ok=True)

def bcast_create(chat,mid,kind,total):
    bid=uuid.uuid4().hex[:16]
    with db() as c:c.execute("INSERT INTO broadcasts(bcast_id,created_at,source_chat_id,source_message_id,kind,total,sent,failed,cancelled,status,last_error,button_url,button_label,button_style) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)",(bid,datetime.now().isoformat(),chat,mid,kind,total,0,0,0,"running","","","",""))
    return bid

def bcast_set_button(bid,url="",label="",style=""):
    with db() as c:c.execute("UPDATE broadcasts SET button_url=?,button_label=?,button_style=? WHERE bcast_id=?",(str(url or ""),str(label or ""),str(style or ""),bid))
def bcast_update(bid,sent,failed,cancelled,status,err=""):
    with db() as c:c.execute("UPDATE broadcasts SET sent=?,failed=?,cancelled=?,status=?,last_error=? WHERE bcast_id=?",(sent,failed,int(cancelled),status,str(err)[:2000],bid))
def bcast_save(bid,uid,mid):
    with db() as c:c.execute("INSERT INTO broadcast_msgs VALUES(?,?,?)",(bid,uid,mid))
def bcast_rows(bid):
    with db() as c:return c.execute("SELECT user_id,message_id FROM broadcast_msgs WHERE bcast_id=?",(bid,)).fetchall()

async def run_broadcast(bot,admin_chat,msg,bid,recipient_list,status_msg):
    sent=failed=0;cancelled=False
    for i,uid in enumerate(recipient_list,1):
        if asyncio.current_task().cancelled():cancelled=True;break
        try:
            kwargs={"chat_id":uid,"from_chat_id":msg.chat_id,"message_id":msg.message_id}
            if getattr(msg,"reply_markup",None) is not None: kwargs["reply_markup"]=msg.reply_markup
            m=await bot.copy_message(**kwargs);bcast_save(bid,uid,m.message_id);sent+=1
        except RetryAfter as e:
            await asyncio.sleep(float(e.retry_after)+.5)
            try:
                kwargs={"chat_id":uid,"from_chat_id":msg.chat_id,"message_id":msg.message_id}
                if getattr(msg,"reply_markup",None) is not None: kwargs["reply_markup"]=msg.reply_markup
                m=await bot.copy_message(**kwargs);bcast_save(bid,uid,m.message_id);sent+=1
            except Exception:failed+=1
        except Forbidden:
            failed+=1;set_status(uid,"inactive")
        except TelegramError as e:failed+=1;logger.warning("Broadcast %s failed for %s: %s",bid,uid,e)
        if i%10==0 or i==len(recipient_list):
            try:await status_msg.edit_text(f"📣 <b>Broadcasting...</b>\n\n📤 Progress: <b>{i}/{len(recipient_list)}</b>\n✅ Sent: <b>{sent}</b>\n❌ Failed: <b>{failed}</b>",reply_markup=safe_markup([[ib("⏹ Cancel Broadcast",f"a_cancelbc_{bid}",style="danger",emoji_id=EMOJI["❌"])] ]),parse_mode=ParseMode.HTML)
            except TelegramError:pass
        await asyncio.sleep(.08)
    status="cancelled" if cancelled else "completed";bcast_update(bid,sent,failed,cancelled,status)
    kb=safe_markup([[ib("🔁 Retry Failed",f"a_retrybc_{bid}",style="success",emoji_id=EMOJI["🌟"])],[ib("🗑 Delete Broadcast",f"a_delbc_{bid}",style="danger",emoji_id=EMOJI["❌"])],[back_button("a_bcast")]])
    try:await status_msg.edit_text(f"{'⏹' if cancelled else '✅'} <b>Broadcast {status.title()}</b>\n\n📤 Total: <b>{len(recipient_list)}</b>\n✅ Sent: <b>{sent}</b>\n❌ Failed: <b>{failed}</b>",reply_markup=kb,parse_mode=ParseMode.HTML)
    except TelegramError:pass

async def _bcast_send_without_button(update,ctx,msg):
    global BROADCAST_TASK
    us=users();bid=bcast_create(msg.chat_id,msg.message_id,"photo" if msg.photo else "video" if msg.video else "text",len(us))
    sm=await update.effective_chat.send_message(f"⏳ Starting broadcast to <b>{len(us)}</b> recipients...",parse_mode=ParseMode.HTML)
    async def runner():
        async with BROADCAST_LOCK:await run_broadcast(ctx.bot,update.effective_chat.id,msg,bid,us,sm)
    BROADCAST_TASK=asyncio.create_task(runner())

async def start_bcast(update,ctx):
    if not is_admin(update.effective_user.id):return ConversationHandler.END
    if gset("broadcast_enabled","1")!="1":await update.message.reply_text("🚫 Broadcast is disabled.");return ConversationHandler.END
    if BROADCAST_LOCK.locked():await update.message.reply_text("⚠️ Another broadcast is already running.");return ConversationHandler.END
    if not (update.message.text or update.message.photo or update.message.video):await update.message.reply_text("❌ Supported: Text, Photo, Video.");return S_BCAST
    ctx.user_data["bcast_source_chat_id"]=update.message.chat_id
    ctx.user_data["bcast_source_message_id"]=update.message.message_id
    ctx.user_data["bcast_source_message"]=update.message
    await update.message.reply_text("Do you want to add an inline button to this broadcast?",reply_markup=safe_markup([[ib("✅ Yes, add a button","bcast_btn_yes",style="success",emoji_id=EMOJI["✅"]),ib("⏭ Skip (send without button)","bcast_btn_skip",style="primary",emoji_id=EMOJI["📌"])],[ib("❌ Cancel Broadcast","bcast_btn_cancel",style="danger",emoji_id=EMOJI["❌"])]]))
    return S_BCAST_BTN_ASK

async def bcast_btn_ask(update,ctx):
    q=update.callback_query
    await q.answer()
    msg=ctx.user_data.get("bcast_source_message")
    if not msg:return ConversationHandler.END
    if q.data=="bcast_btn_cancel":
        ctx.user_data.clear();await q.edit_message_text("❌ Cancelled.");return ConversationHandler.END
    if q.data=="bcast_btn_skip":
        await _bcast_send_without_button(update,ctx,msg)
        ctx.user_data.clear()
        return ConversationHandler.END
    if q.data=="bcast_btn_yes":
        await q.edit_message_text("Send the button LINK (URL).\n\nUse an http(s) URL or t.me/... Telegram link.\n\nSend /cancel to cancel.")
        return S_BCAST_BTN_LINK
    return S_BCAST_BTN_ASK

def _valid_bcast_url(value):
    v=str(value or "").strip()
    candidate=v if v.lower().startswith(("http://","https://")) else ("https://"+v if v.lower().startswith("t.me/") else "")
    if not candidate:return None
    try:
        p=urlparse(candidate)
        if p.scheme not in ("http","https") or not p.netloc:return None
        host=p.netloc.split(":",1)[0].lower()
        if v.lower().startswith("t.me/") and host!="t.me":return None
        if not v.lower().startswith("t.me/") and p.scheme not in ("http","https"):return None
        return candidate
    except Exception:return None

async def bcast_btn_link(update,ctx):
    if not update.message or not update.message.text:return S_BCAST_BTN_LINK
    url=_valid_bcast_url(update.message.text)
    if not url:
        await update.message.reply_text("❌ Invalid link. Send a valid http(s) URL or t.me/... Telegram link, or /cancel.")
        return S_BCAST_BTN_LINK
    ctx.user_data["bcast_button_url"]=url
    await update.message.reply_text("Send the button NAME/label.\n\nSend /cancel to cancel.")
    return S_BCAST_BTN_NAME

async def bcast_btn_name(update,ctx):
    if not update.message or not update.message.text:return S_BCAST_BTN_NAME
    label=safe_button_text(update.message.text)
    if not label or len(label)>64:
        await update.message.reply_text("❌ Invalid button name. Send visible text up to 64 characters, or /cancel.")
        return S_BCAST_BTN_NAME
    ctx.user_data["bcast_button_label"]=label
    await update.message.reply_text("Choose the button color/style.",reply_markup=safe_markup([[ib("🔵 Primary","bcast_style_primary",style="primary"),ib("🟢 Success","bcast_style_success",style="success")],[ib("🔴 Danger","bcast_style_danger",style="danger")],[ib("❌ Cancel","bcast_btn_cancel",style="danger",emoji_id=EMOJI["❌"])]]))
    return S_BCAST_BTN_STYLE

async def bcast_btn_style(update,ctx):
    q=update.callback_query;await q.answer()
    if q.data=="bcast_btn_cancel":
        ctx.user_data.clear();await q.edit_message_text("❌ Cancelled.");return ConversationHandler.END
    if not q.data.startswith("bcast_style_"):return S_BCAST_BTN_STYLE
    style=q.data[len("bcast_style_"):]
    if style not in BUTTON_STYLES:return S_BCAST_BTN_STYLE
    ctx.user_data["bcast_button_style"]=style
    msg=ctx.user_data.get("bcast_source_message")
    url=ctx.user_data.get("bcast_button_url","");label=ctx.user_data.get("bcast_button_label","")
    button=ib(label,url=url,style=style)
    if not msg or not button:
        await q.edit_message_text("❌ Unable to build the button. Send /cancel to abort.")
        return S_BCAST_BTN_STYLE
    preview=await ctx.bot.copy_message(q.message.chat_id,msg.chat_id,msg.message_id,reply_markup=safe_markup([[button]]))
    ctx.user_data["bcast_preview_message_id"]=preview.message_id
    await q.edit_message_text("<b>Preview ready.</b>\n\nConfirm to send this broadcast.",reply_markup=safe_markup([[ib("📤 Send Broadcast Now","bcast_confirm",style="success",emoji_id=EMOJI["📣"])],[ib("❌ Cancel Broadcast","bcast_cancel",style="danger",emoji_id=EMOJI["❌"])]]),parse_mode=ParseMode.HTML)
    return S_BCAST_PREVIEW

async def bcast_preview(update,ctx):
    q=update.callback_query;await q.answer()
    if q.data=="bcast_cancel":
        ctx.user_data.clear();await q.edit_message_text("❌ Cancelled.");return ConversationHandler.END
    if q.data!="bcast_confirm":return S_BCAST_PREVIEW
    if BROADCAST_LOCK.locked():
        await q.answer("Another broadcast is already running.",show_alert=True);return S_BCAST_PREVIEW
    msg=ctx.user_data.get("bcast_source_message")
    url=ctx.user_data.get("bcast_button_url","");label=ctx.user_data.get("bcast_button_label","");style=ctx.user_data.get("bcast_button_style","")
    if not msg or style not in BUTTON_STYLES or not _valid_bcast_url(url) or not label:
        await q.answer("Broadcast setup is incomplete.",show_alert=True);return S_BCAST_PREVIEW
    us=users();bid=bcast_create(msg.chat_id,msg.message_id,"photo" if msg.photo else "video" if msg.video else "text",len(us));bcast_set_button(bid,url,label,style)
    button=ib(label,url=url,style=style)
    send_msg=SimpleNamespace(chat_id=msg.chat_id,message_id=msg.message_id,reply_markup=safe_markup([[button]]))
    sm=await q.message.reply_text(f"⏳ Starting broadcast to <b>{len(us)}</b> recipients...",parse_mode=ParseMode.HTML)
    global BROADCAST_TASK
    async def runner():
        async with BROADCAST_LOCK:await run_broadcast(ctx.bot,q.message.chat_id,send_msg,bid,us,sm)
    BROADCAST_TASK=asyncio.create_task(runner())
    ctx.user_data.clear()
    return ConversationHandler.END

async def cancel_bcast(q,bid):
    global BROADCAST_TASK
    if BROADCAST_TASK and not BROADCAST_TASK.done():
        BROADCAST_TASK.cancel()
        try:await BROADCAST_TASK
        except asyncio.CancelledError:pass
    bcast_update(bid,0,0,True,"cancelled")

async def input_text(update,ctx,key,label,clear=False):
    if not update.message.text:return False
    v=update.message.text.strip();v="" if clear and v.lower()=="clear" else update.message.text_html.strip();sset(key,v)
    await update.message.reply_text("✅ "+label+" updated.",reply_markup=back_kb("a_msgs"));return True

async def s_top(u,c):return ConversationHandler.END if await input_text(u,c,"top","Top Message",True) else S_TOP
async def s_welcome(u,c):return ConversationHandler.END if await input_text(u,c,"welcome","Welcome Message") else S_WELCOME
async def s_postjoin(u,c):return ConversationHandler.END if await input_text(u,c,"postjoin","Post-Join Message") else S_POSTJOIN
async def s_btn1(u,c):return ConversationHandler.END if await input_text(u,c,"btn1_msg","Button 1 Reply") else S_BTN1
async def s_btn2(u,c):return ConversationHandler.END if await input_text(u,c,"btn2_msg","Button 2 Reply") else S_BTN2
async def s_btn3(u,c):return ConversationHandler.END if await input_text(u,c,"btn3_msg","Button 3 Reply") else S_BTN3

async def s_photo(u,c):
    if u.message.text and u.message.text.strip().lower()=="clear":sset("welcome_photo","");await u.message.reply_text("✅ Welcome photo cleared.",reply_markup=back_kb("a_msgs"));return ConversationHandler.END
    if not u.message.photo:await u.message.reply_text("❌ Send a photo or 'clear'.",reply_markup=back_kb("a_msgs"));return S_WELCOME_PHOTO
    sset("welcome_photo",u.message.photo[-1].file_id);await u.message.reply_text("✅ Welcome photo updated.",reply_markup=back_kb("a_msgs"));return ConversationHandler.END

async def s_ch_id(u,c):c.user_data["ch_id"]=(u.message.text or "").strip();await u.message.reply_text("✏️ Send Channel Name:",reply_markup=back_kb("a_chs"));return S_CH_NAME
async def s_ch_name(u,c):
    name=_clean_visible_label(u.message.text or "")
    if not name:
        await u.message.reply_text("❌ Channel name cannot be empty. Send a valid channel name.",reply_markup=back_kb("a_chs"))
        return S_CH_NAME
    c.user_data["ch_name"]=name
    await u.message.reply_text("🔗 Send Channel Invite Link:",reply_markup=back_kb("a_chs"))
    return S_CH_LINK
async def s_ch_link(u,c):
    link=(u.message.text or "").strip()
    if not link.startswith(("https://t.me/","http://t.me/")):await u.message.reply_text("❌ Invalid Telegram link.",reply_markup=back_kb("a_chs"));return S_CH_LINK
    try:
        add_channel(c.user_data["ch_id"],c.user_data["ch_name"],link)
    except sqlite3.IntegrityError:
        await u.message.reply_text("❌ Channel already exists.");return ConversationHandler.END
    except ValueError as e:
        await u.message.reply_text("❌ "+esc(e),reply_markup=back_kb("a_chs"));return S_CH_NAME
    c.user_data.clear();await u.message.reply_text("✅ Channel added.",reply_markup=back_kb("a_chs"));return ConversationHandler.END

async def s_editname(u,c):
    cid=c.user_data.get("edit_channel")
    if not cid:return ConversationHandler.END
    name=_clean_visible_label(u.message.text or "")
    if not name:
        await u.message.reply_text("❌ Channel name cannot be empty. Send a valid channel name.",reply_markup=back_kb("a_chs"))
        return S_EDITNAME
    update_channel(cid,name=name)
    await u.message.reply_text("🔗 Send new invite link or <code>skip</code>.",reply_markup=back_kb("a_chs"),parse_mode=ParseMode.HTML)
    return S_EDITLINK
async def s_editlink(u,c):
    cid=c.user_data.get("edit_channel");v=(u.message.text or "").strip()
    if v.lower()!="skip":
        if not v.startswith(("https://t.me/","http://t.me/")):await u.message.reply_text("❌ Invalid Telegram link.",reply_markup=back_kb("a_chs"));return S_EDITLINK
        update_channel(cid,link=v)
    c.user_data.clear();await u.message.reply_text("✅ Channel updated.",reply_markup=back_kb("a_chs"));return ConversationHandler.END

async def s_button_name(u,c):
    """Save managed button names plus dedicated force-join labels."""
    mode=c.user_data.get("join_edit_mode")
    value=(u.message.text or "").strip()
    if mode:
        if not safe_button_text(value):
            await u.message.reply_text("❌ Name must contain visible text, not emoji/invisible characters only. Send a valid name.",reply_markup=back_kb("a_joinbuttons"))
            return S_BTN_NAME
        if mode=="channel_name_template":
            cfg=get_button_config("ui_join_channel") or BUTTON_DEFAULTS["ui_join_channel"]
            save_button_config("ui_join_channel",label=value)
        elif mode=="joined_name":
            save_button_config("ui_join_check",label=value)
        c.user_data.pop("join_edit_mode",None)
        await u.message.reply_text("✅ <b>Force-join button name updated.</b>",reply_markup=safe_markup([[back_button("a_joinbuttons")]]),parse_mode=ParseMode.HTML)
        return ConversationHandler.END

    key=c.user_data.get("button_edit_key")
    if not key or key not in BUTTON_DEFAULTS:
        c.user_data.clear()
        await u.message.reply_text("❌ Button edit session expired. Please open the button editor again.",reply_markup=back_kb("a_buttons"))
        return ConversationHandler.END
    if not safe_button_text(value):
        await u.message.reply_text("❌ Button name must contain visible text. Send a valid name or press Back.",reply_markup=back_kb(f"a_editbutton_{key}"))
        return S_BTN_NAME
    save_button_config(key,label=value)
    await u.message.reply_text("✅ <b>Button name updated.</b>\n\n"+render_button_editor_text(key),reply_markup=button_editor_kb(key),parse_mode=ParseMode.HTML)
    c.user_data.clear()
    return ConversationHandler.END

async def s_button_normal(u,c):
    """Save a normal Unicode emoji for the selected managed button."""
    key=c.user_data.get("button_edit_key")
    if not key or key not in BUTTON_DEFAULTS:
        c.user_data.clear()
        await u.message.reply_text("❌ Button edit session expired. Please open the button editor again.",reply_markup=back_kb("a_buttons"))
        return ConversationHandler.END
    value=(u.message.text or "").strip()
    if value.lower()=="clear":
        value=""
    elif len(value)>16:
        await u.message.reply_text("❌ Please send one normal Unicode emoji, or <code>clear</code>.",reply_markup=back_kb(f"a_editbutton_{key}"),parse_mode=ParseMode.HTML)
        return S_BTN_NORMAL
    save_button_config(key,normal_emoji=value)
    await u.message.reply_text("✅ <b>Normal emoji updated.</b>\n\n"+render_button_editor_text(key),reply_markup=button_editor_kb(key),parse_mode=ParseMode.HTML)
    c.user_data.clear()
    return ConversationHandler.END

async def s_button_premium(u,c):
    """Accept either a numeric custom-emoji ID or a Telegram custom emoji message."""
    join_mode=c.user_data.get("join_edit_mode")
    key=c.user_data.get("button_edit_key")
    if not join_mode and (not key or key not in BUTTON_DEFAULTS):
        c.user_data.clear()
        await u.message.reply_text("❌ Button edit session expired. Please open the button editor again.",reply_markup=back_kb("a_buttons"))
        return ConversationHandler.END

    raw=(u.message.text or u.message.caption or "").strip()
    if raw.lower()=="clear":
        if join_mode=="channel_emoji":
            save_button_config("ui_join_channel",premium_emoji_id="",premium_enabled=False)
            c.user_data.pop("join_edit_mode",None)
            await u.message.reply_text("✅ <b>Channel premium emoji cleared.</b>",reply_markup=back_kb("a_joinbuttons"),parse_mode=ParseMode.HTML)
            return ConversationHandler.END
        if join_mode=="joined_emoji":
            save_button_config("ui_join_check",premium_emoji_id="",premium_enabled=False)
            c.user_data.pop("join_edit_mode",None)
            await u.message.reply_text("✅ <b>Verify premium emoji cleared.</b>",reply_markup=back_kb("a_joinbuttons"),parse_mode=ParseMode.HTML)
            return ConversationHandler.END
        save_button_config(key,premium_emoji_id="",premium_enabled=False)
        await u.message.reply_text("✅ <b>Premium custom emoji cleared.</b>\n\n"+render_button_editor_text(key),reply_markup=button_editor_kb(key),parse_mode=ParseMode.HTML)
        c.user_data.clear()
        return ConversationHandler.END

    custom_id=None
    entities=list(u.message.entities or [])+list(u.message.caption_entities or [])
    for entity in entities:
        etype=str(getattr(entity,"type","")).lower()
        if etype.endswith("custom_emoji") or etype=="custom_emoji":
            candidate=getattr(entity,"custom_emoji_id",None)
            if candidate:
                custom_id=str(candidate)
                break
    if not custom_id and raw.isdigit():
        custom_id=raw

    if not custom_id:
        target_back="a_joinbuttons" if join_mode else f"a_editbutton_{key}"
        await u.message.reply_text("❌ Could not detect a Telegram Custom Emoji ID.\n\nSend the premium/custom emoji itself, or send its numeric ID.\n\nYou can also send <code>clear</code> to remove it.",reply_markup=back_kb(target_back),parse_mode=ParseMode.HTML)
        return S_BTN_PREMIUM

    if join_mode=="channel_emoji":
        save_button_config("ui_join_channel",premium_emoji_id=custom_id,premium_enabled=True)
        c.user_data.pop("join_edit_mode",None)
        await u.message.reply_text("✅ <b>Channel premium emoji updated.</b>",reply_markup=back_kb("a_joinbuttons"),parse_mode=ParseMode.HTML)
        return ConversationHandler.END
    if join_mode=="joined_emoji":
        save_button_config("ui_join_check",premium_emoji_id=custom_id,premium_enabled=True)
        c.user_data.pop("join_edit_mode",None)
        await u.message.reply_text("✅ <b>Verify premium emoji updated.</b>",reply_markup=back_kb("a_joinbuttons"),parse_mode=ParseMode.HTML)
        return ConversationHandler.END

    save_button_config(key,premium_emoji_id=custom_id,premium_enabled=True)
    await u.message.reply_text("✅ <b>Premium custom emoji updated.</b>\n\nDetected ID: <code>"+esc(custom_id)+"</code>\n\n"+render_button_editor_text(key),reply_markup=button_editor_kb(key),parse_mode=ParseMode.HTML)
    c.user_data.clear()
    return ConversationHandler.END

async def s_force_join_message(u,c):
    if not is_admin(u.effective_user.id):
        c.user_data.clear(); return ConversationHandler.END
    raw=(u.message.text_html if getattr(u.message,"text_html",None) is not None else (u.message.text or "")).strip()
    if raw.lower()=="clear": raw=""
    sset("force_join_message",raw)
    await u.message.reply_text("✅ <b>Force Join message updated.</b>" if raw else "✅ <b>Force Join message cleared.</b>",reply_markup=back_kb("a_joinbuttons"),parse_mode=ParseMode.HTML)
    return ConversationHandler.END

async def s_emoji(u,c):
    c.user_data["button_edit_key"]=c.user_data.get("emoji_key") or c.user_data.get("button_edit_key")
    return await s_button_premium(u,c)


async def s_restore(u,c):
    if not is_admin(u.effective_user.id):return ConversationHandler.END
    d=u.message.document
    if not d or not (d.file_name or "").lower().endswith(".zip"):await u.message.reply_text("❌ Send a backup .zip file.");return S_RESTORE
    p=None
    try:
        f=await c.bot.get_file(d.file_id)
        with tempfile.NamedTemporaryFile(suffix=".zip",delete=False) as t:p=t.name
        await f.download_to_drive(p);safety=restore_backup(p)
        await u.message.reply_text("✅ <b>Restore completed.</b>\n\n🔐 Safety backup created.\n♻️ Restored configuration and database are now active.",parse_mode=ParseMode.HTML)
    except Exception as e:logger.exception("Restore");await u.message.reply_text("❌ Restore failed:\n<code>"+esc(e)+"</code>",parse_mode=ParseMode.HTML)
    finally:
        if p:
            try:os.remove(p)
            except OSError:pass
    return ConversationHandler.END

async def s_search(u,c):
    rows=search_users(u.message.text or "")
    if not rows:await u.message.reply_text("❌ No users found.",reply_markup=back_kb("a_members"));return ConversationHandler.END
    kb=[]
    for r in rows:kb.append([ib("👁 View",f"a_viewu_{r[0]}",style="primary",emoji_id=EMOJI["📊"]),ib("🚫 Block",f"a_blocku_{r[0]}",style="danger",emoji_id=EMOJI["❌"])])
    await u.message.reply_text("\n".join(f"👤 <b>{esc(r[1])}</b> · <code>{r[0]}</code> · @{esc(r[2]) if r[2] else '—'} · {esc(r[4])}" for r in rows),reply_markup=safe_markup(kb),parse_mode=ParseMode.HTML);return ConversationHandler.END

async def s_usermsg(u,c):
    uid=c.user_data.get("msg_uid")
    try:await c.bot.copy_message(uid,u.message.chat_id,u.message.message_id);await u.message.reply_text("✅ Message sent.",reply_markup=back_kb("a_members"))
    except TelegramError as e:await u.message.reply_text("❌ Send failed: "+esc(e),reply_markup=back_kb("a_members"))
    c.user_data.clear();return ConversationHandler.END

async def admin_cb(update,ctx):
    q=update.callback_query
    if not is_admin(q.from_user.id):await q.answer("❌ Not authorized!",show_alert=True);return ConversationHandler.END
    await q.answer();d=q.data or ""
    # User-management callbacks are handled here because the admin ConversationHandler
    # owns all ^a_ callbacks.
    if d.startswith("a_viewu_"):
        uid=int(d.split("_")[-1])
        with db() as c:r=c.execute("SELECT user_id,first_name,username,joined_at,status FROM users WHERE user_id=?",(uid,)).fetchone()
        if not r:return await q.answer("User not found.",show_alert=True)
        await q.edit_message_text(
            f"👤 <b>USER</b>\n\nID: <code>{r[0]}</code>\nFirst Name: <b>{esc(r[1])}</b>\n"
            f"Username: <b>@{esc(r[2]) if r[2] else '—'}</b>\nJoin Date: <code>{esc(r[3])}</code>\nStatus: <b>{esc(r[4])}</b>",
            reply_markup=safe_markup([
                [ib("💬 Send Message",f"a_msgu_{uid}",style="primary",emoji_id=EMOJI["💬"])],
                [ib("🚫 Block",f"a_blocku_{uid}",style="danger",emoji_id=EMOJI["❌"]),
                 ib("✅ Unblock",f"a_unblocku_{uid}",style="success",emoji_id=EMOJI["✅"])],
                [ib("🗑 Delete",f"a_deleteu_{uid}",style="danger",emoji_id=EMOJI["❌"])],
                [back_button("a_members")]
            ]),parse_mode=ParseMode.HTML)
        return ConversationHandler.END
    if d.startswith("a_blocku_"):
        uid=int(d.split("_")[-1])
        await q.edit_message_text("⚠️ <b>Are you sure?</b>\n\nBlock this user?",
            reply_markup=safe_markup([[ib("✅ Confirm",f"a_confirmblock_{uid}",style="danger",emoji_id=EMOJI["❌"]),
                                                 ib("❌ Cancel",f"a_viewu_{uid}",style="primary",emoji_id=EMOJI["📌"])]]),
            parse_mode=ParseMode.HTML)
        return ConversationHandler.END
    if d.startswith("a_confirmblock_"):
        set_status(int(d.split("_")[-1]),"blocked")
        await q.edit_message_text("🚫 User blocked.",reply_markup=back_kb("a_members"))
        return ConversationHandler.END
    if d.startswith("a_unblocku_"):
        set_status(int(d.split("_")[-1]),"active")
        await q.edit_message_text("✅ User unblocked.",reply_markup=back_kb("a_members"))
        return ConversationHandler.END
    if d.startswith("a_deleteu_"):
        uid=int(d.split("_")[-1])
        await q.edit_message_text("⚠️ <b>Are you sure?</b>\n\nDelete this user permanently?",
            reply_markup=safe_markup([[ib("✅ Confirm",f"a_confirmdeleteu_{uid}",style="danger",emoji_id=EMOJI["❌"]),
                                                 ib("❌ Cancel",f"a_viewu_{uid}",style="primary",emoji_id=EMOJI["📌"])]]),
            parse_mode=ParseMode.HTML)
        return ConversationHandler.END
    if d.startswith("a_confirmdeleteu_"):
        delete_user(int(d.split("_")[-1]))
        await q.edit_message_text("🗑 User deleted.",reply_markup=back_kb("a_members"))
        return ConversationHandler.END
    if d.startswith("a_msgu_"):
        ctx.user_data["msg_uid"]=int(d.split("_")[-1])
        await q.edit_message_text("💬 Send the message to deliver to this user.",reply_markup=back_kb("a_members"))
        return S_USERMSG

    if d in ("a_back","a_dash"):await q.edit_message_text(dash(),reply_markup=admin_kb(),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d=="a_close":await q.edit_message_text("❌ Admin panel closed.");return ConversationHandler.END
    if d=="a_chs":await show_channels(q);return ConversationHandler.END
    if d=="a_addch":await q.edit_message_text("📢 <b>Add Channel</b>\n\nSend Channel ID.",reply_markup=back_kb("a_chs"),parse_mode=ParseMode.HTML);return S_CH_ID
    if d.startswith("a_delc_"):
        cid=int(d.split("_")[-1]);ctx.user_data["confirm"]=("delc",cid)
        await q.edit_message_text("⚠️ <b>Are you sure?</b>\n\nDelete this channel?",reply_markup=safe_markup([[ib("✅ Confirm",f"a_confirm_{cid}",style="danger",emoji_id=EMOJI["❌"]),ib("❌ Cancel","a_chs",style="primary",emoji_id=EMOJI["📌"])] ]),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d.startswith("a_confirm_"):
        cid=int(d.split("_")[-1]);a,t=ctx.user_data.pop("confirm",("",None))
        if a=="delc" and t==cid:delete_channel(cid)
        await show_channels(q);return ConversationHandler.END
    if d.startswith("a_left_"):move_channel(int(d.split("_")[-1]),"left");await show_channels(q);return ConversationHandler.END
    if d.startswith("a_right_"):move_channel(int(d.split("_")[-1]),"right");await show_channels(q);return ConversationHandler.END
    if d.startswith("a_togglec_"):toggle_channel(int(d.split("_")[-1]));await show_channels(q);return ConversationHandler.END
    if d.startswith("a_testc_"):
        r=channel(int(d.split("_")[-1]));ok,adm,title,status=await channel_status(ctx.bot,r[1])
        await q.edit_message_text(f"🧪 <b>Channel Status</b>\n\nName: <b>{esc(r[2])}</b>\nAccessible: {'✅ YES' if ok else '❌ NO'}\nBot Admin: {'✅ YES' if adm else '❌ NO'}\nStatus: <code>{esc(status)}</code>",reply_markup=back_kb("a_chs"),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d.startswith("a_editc_"):
        ctx.user_data["edit_channel"]=int(d.split("_")[-1]);await q.edit_message_text("✏️ Send new channel name:",reply_markup=back_kb("a_chs"));return S_EDITNAME
    if d=="a_msgs":await q.edit_message_text("📝 <b>MESSAGE MANAGEMENT</b>\n\nHTML formatting is preserved.",reply_markup=msg_kb(),parse_mode=ParseMode.HTML);return ConversationHandler.END
    mm={"a_top":("top","Top Message",S_TOP),"a_welcome":("welcome","Welcome Message",S_WELCOME),"a_postjoin":("postjoin","Post-Join Message",S_POSTJOIN),"a_btn1":("btn1_msg",_legacy_names("btn1"),S_BTN1),"a_btn2":("btn2_msg",_legacy_names("btn2"),S_BTN2),"a_btn3":("btn3_msg",_legacy_names("btn3"),S_BTN3)}
    if d in mm:
        k,n,s=mm[d];await q.edit_message_text(f"✏️ <b>{esc(n)}</b>\n\nCurrent:\n<pre>{esc(gset(k)[:1500])}</pre>\n\nSend new text.",reply_markup=back_kb("a_msgs"),parse_mode=ParseMode.HTML);return s
    if d=="a_welcome_photo":await q.edit_message_text("🖼 <b>Welcome Photo</b>\n\nSend a photo or <code>clear</code>.",reply_markup=back_kb("a_msgs"),parse_mode=ParseMode.HTML);return S_WELCOME_PHOTO
    if d=="a_buttons":
        await q.edit_message_text("🎨 <b>BUTTON MANAGEMENT</b>\n\nChoose public, admin, or force-join buttons. All visible buttons use premium custom emoji only.",reply_markup=btn_kb(),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d=="a_forcejoin_message":
        current=get_force_join_message()
        await q.edit_message_text("📝 <b>FORCE JOIN MESSAGE</b>\n\nThis is the only custom instruction text shown on Force Join.\nSend replacement text or <code>clear</code> to make it empty.\n\nCurrent:\n<pre>"+esc(current[:3000])+"</pre>",reply_markup=back_kb("a_joinbuttons"),parse_mode=ParseMode.HTML)
        return S_FORCE_JOIN_MSG
    if d=="a_forcejoin_clear":
        sset("force_join_message","")
        await q.edit_message_text("✅ <b>Force Join message cleared.</b>",reply_markup=back_kb("a_joinbuttons"),parse_mode=ParseMode.HTML)
        return ConversationHandler.END
    if d=="a_forcejoin_reset":
        sset("force_join_message","")
        await q.edit_message_text("✅ <b>Force Join message reset.</b>",reply_markup=back_kb("a_joinbuttons"),parse_mode=ParseMode.HTML)
        return ConversationHandler.END
    if d=="a_forcejoin_preview":
        sample=[(1,"-100000000001","Channel 1","https://t.me/example1",0,1,1),(2,"-100000000002","Channel 2","https://t.me/example2",0,2,1)]
        try:
            await render_force_join(ctx.bot,q.message.chat_id,rows=sample,joined=set())
        except TelegramError as e:
            logger.warning("ForceJoin preview failed: %s",e)
        return ConversationHandler.END
    if d=="a_joinbuttons":
        jc=get_button_config("ui_join_channel") or BUTTON_DEFAULTS["ui_join_channel"]
        jj=get_button_config("ui_join_check") or BUTTON_DEFAULTS["ui_join_check"]
        txt=("🔗 <b>FORCE-JOIN BUTTONS</b>\n\n"
             "Channel template: <code>"+esc(jc.get("label") or "{name}")+"</code>\n"
             "Channel premium emoji ID: <code>"+esc(jc.get("premium_emoji_id") or "None")+"</code>\n"
             "Verify button name: <code>"+esc(jj.get("label") or "Joined")+"</code>\n"
             "Verify premium emoji ID: <code>"+esc(jj.get("premium_emoji_id") or "None")+"</code>\n\n"
             "Use <code>{name}</code> in the channel template to keep the configured channel name dynamic.")
        kb=safe_markup([
            [ib("Channel Button Name/Template","a_join_name",style="primary",emoji_id=EMOJI["📝"])],
            [ib("Channel Premium Emoji","a_join_emoji",style="success",emoji_id=EMOJI["👑"])],
            [ib("Verify Button Name","a_joined_name",style="primary",emoji_id=EMOJI["📝"])],
            [ib("Verify Premium Emoji","a_joined_emoji",style="success",emoji_id=EMOJI["👑"])],
            [ib("Edit Force Join Message","a_forcejoin_message",style="primary",emoji_id=EMOJI["📝"] )],
            [ib("Preview Force Join","a_forcejoin_preview",style="success",emoji_id=EMOJI["📌"])],
            [ib("Clear Force Join Message","a_forcejoin_clear",style="danger",emoji_id=EMOJI["❌"]),ib("Reset Force Join","a_forcejoin_reset",style="danger",emoji_id=EMOJI["❌"])],
            [back_button("a_buttons")]])
        await q.edit_message_text(txt,reply_markup=kb,parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d in ("a_public_buttons","a_admin_buttons"):
        prefix="public" if d=="a_public_buttons" else "admin"
        title="PUBLIC BUTTONS" if prefix=="public" else "ADMIN PANEL BUTTONS"
        await q.edit_message_text("🎨 <b>"+title+"</b>\n\nSelect a button to edit its name, premium custom emoji, premium state, style, order and enabled state.",reply_markup=button_list_kb(prefix),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d.startswith("a_show_disabled_"):
        prefix=d[len("a_show_disabled_"):]
        keys=[k for k in BUTTON_DEFAULTS if ((k.startswith("ui_a_") and prefix=="admin") or (not k.startswith("ui_") and prefix=="public")) and not get_button_config(k).get("enabled")]
        rows=[]
        for key in keys: rows.append([ib(get_button_config(key)["label"][:28],"a_editbutton_"+key,style=get_button_config(key)["style"],emoji_id=get_button_config(key).get("premium_emoji_id"))])
        rows.append([back_button("a_public_buttons" if prefix=="public" else "a_admin_buttons")])
        await q.edit_message_text("🎨 <b>DISABLED BUTTONS</b>\n\nSelect a button to edit or re-enable it.",reply_markup=safe_markup(rows),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d=="a_join_name":
        ctx.user_data["join_edit_mode"]="channel_name_template"
        current=(get_button_config("ui_join_channel") or BUTTON_DEFAULTS["ui_join_channel"]).get("label") or "{name}"
        await q.edit_message_text("✏️ <b>Channel Button Name / Template</b>\n\nSend the button label template. Use <code>{name}</code> where the channel name should appear.\n\nCurrent: <code>"+esc(current)+"</code>",reply_markup=back_kb("a_joinbuttons"),parse_mode=ParseMode.HTML);return S_BTN_NAME
    if d=="a_join_emoji":
        ctx.user_data["join_edit_mode"]="channel_emoji"
        current=(get_button_config("ui_join_channel") or BUTTON_DEFAULTS["ui_join_channel"]).get("premium_emoji_id") or "None"
        await q.edit_message_text("👑 <b>Channel Premium Emoji</b>\n\nSend the Telegram Custom Emoji itself or its numeric ID. Send <code>clear</code> to remove it.\n\nCurrent: <code>"+esc(current)+"</code>",reply_markup=back_kb("a_joinbuttons"),parse_mode=ParseMode.HTML);return S_BTN_PREMIUM
    if d=="a_joined_name":
        ctx.user_data["join_edit_mode"]="joined_name"
        current=(get_button_config("ui_join_check") or BUTTON_DEFAULTS["ui_join_check"]).get("label") or "Joined"
        await q.edit_message_text("✏️ <b>Verify Button Name</b>\n\nSend the new name, e.g. <code>Continue</code>.\n\nCurrent: <code>"+esc(current)+"</code>",reply_markup=back_kb("a_joinbuttons"),parse_mode=ParseMode.HTML);return S_BTN_NAME
    if d=="a_joined_emoji":
        ctx.user_data["join_edit_mode"]="joined_emoji"
        current=(get_button_config("ui_join_check") or BUTTON_DEFAULTS["ui_join_check"]).get("premium_emoji_id") or "None"
        await q.edit_message_text("👑 <b>Verify Premium Emoji</b>\n\nSend the Telegram Custom Emoji itself or its numeric ID. Send <code>clear</code> to remove it.\n\nCurrent: <code>"+esc(current)+"</code>",reply_markup=back_kb("a_joinbuttons"),parse_mode=ParseMode.HTML);return S_BTN_PREMIUM
    if d.startswith("a_editbutton_"):
        key=d[len("a_editbutton_"):]
        if key not in BUTTON_DEFAULTS or not is_admin(q.from_user.id):return ConversationHandler.END
        txt=render_button_editor_text(key)
        preview=render_button(key)
        kb=button_editor_kb(key)
        await q.edit_message_text(txt,reply_markup=kb,parse_mode=ParseMode.HTML)
        if preview:
            await q.message.reply_text("👁 <b>Current Preview</b>",reply_markup=safe_markup([[preview]]),parse_mode=ParseMode.HTML)
        return ConversationHandler.END
    if d.startswith("a_btnname_"):
        key=d[len("a_btnname_"):]
        if key not in BUTTON_DEFAULTS:return ConversationHandler.END
        ctx.user_data["button_edit_key"]=key;await q.edit_message_text("✏️ <b>Edit Button Name</b>\n\nSend the new button name:\n\nCurrent: <code>"+esc(get_button_config(key)["label"])+"</code>",reply_markup=back_kb(f"a_editbutton_{key}"),parse_mode=ParseMode.HTML);return S_BTN_NAME
    if d.startswith("a_btnpremium_"):
        key=d[len("a_btnpremium_"):]
        if key not in BUTTON_DEFAULTS:return ConversationHandler.END
        ctx.user_data["button_edit_key"]=key;await q.edit_message_text("👑 <b>Set Premium Custom Emoji</b>\n\nSend the premium/custom emoji itself (easy mode) and I will automatically detect its Telegram Custom Emoji ID.\n\nYou can also send a numeric Telegram custom emoji ID.\nExample: <code>5228855127892327218</code>\nSend <code>clear</code> to remove the premium emoji.\n\nCurrent: <code>"+esc(get_button_config(key).get("premium_emoji_id") or "None")+"</code>",reply_markup=back_kb(f"a_editbutton_{key}"),parse_mode=ParseMode.HTML);return S_BTN_PREMIUM
    if d.startswith("a_btntoggle_"):
        key=d[len("a_btntoggle_"):];cfg=get_button_config(key)
        save_button_config(key,premium_enabled=not cfg.get("premium_enabled"));await q.edit_message_text("✅ Premium emoji setting updated.",reply_markup=button_editor_kb(key),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d=="a_global_premium":
        await q.answer("Premium custom emoji mode is fixed ON for buttons.",show_alert=True)
        await q.edit_message_text("Premium custom emoji mode is fixed <b>ON</b> for all buttons.",reply_markup=btn_kb(),parse_mode=ParseMode.HTML)
        return ConversationHandler.END
    if d.startswith("a_style_"):
        key=d[len("a_style_"):];cfg=get_button_config(key)
        nxt={"primary":"success","success":"danger","danger":"primary"}[cfg["style"]];save_button_config(key,style=nxt);await q.edit_message_text("🎨 <b>Style updated</b>\n\nCurrent: <code>"+nxt+"</code>",reply_markup=button_editor_kb(key),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d.startswith("a_moveup_") or d.startswith("a_movedown_"):
        key=d.split("_",2)[2];cfg=get_button_config(key)
        peers=[k for k in BUTTON_DEFAULTS if (k.startswith("ui_a_") and key.startswith("ui_a_")) or (not k.startswith("ui_") and not key.startswith("ui_"))]
        peers=sorted(peers,key=lambda k:get_button_config(k)["position"])
        i=peers.index(key);j=i-1 if d.startswith("a_moveup_") else i+1
        if 0<=j<len(peers):
            other=peers[j];op=get_button_config(other)["position"];save_button_config(key,position=op);save_button_config(other,position=cfg["position"])
        await q.edit_message_text(render_button_editor_text(key),reply_markup=button_editor_kb(key),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d.startswith("a_enable_"):
        key=d[len("a_enable_"):];cfg=get_button_config(key);save_button_config(key,enabled=not cfg.get("enabled"));await q.edit_message_text("✅ Button enabled state updated.",reply_markup=button_editor_kb(key),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d=="a_reset_all":
        await q.edit_message_text("⚠️ <b>Are you sure you want to reset ALL button configurations?</b>\n\nOnly button UI configuration will be reset. Users, channels, messages, broadcasts and other data are untouched.",reply_markup=safe_markup([[ib("✅ Confirm","a_reset_all_confirm",style="danger",emoji_id=EMOJI["❌"]),ib("❌ Cancel","a_buttons",style="primary",emoji_id=EMOJI["📌"])]]),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d=="a_reset_all_confirm":
        try:reset_all_button_configs();await q.edit_message_text("✅ <b>All button configurations reset to defaults.</b>",reply_markup=btn_kb(),parse_mode=ParseMode.HTML)
        except Exception as e:logger.exception("Reset all buttons");await q.edit_message_text("❌ Reset failed:\n<code>"+esc(e)+"</code>",reply_markup=btn_kb(),parse_mode=ParseMode.HTML)
        return ConversationHandler.END
    if d.startswith("a_reset_"):
        key=d[len("a_reset_"):]
        if key in BUTTON_DEFAULTS:
            reset_button_config(key);await q.edit_message_text("✅ <b>Button reset to default configuration.</b>",reply_markup=button_editor_kb(key),parse_mode=ParseMode.HTML);return ConversationHandler.END
        return ConversationHandler.END
    if d.startswith("a_preview_"):
        key=d[len("a_preview_"):]
        b=render_button(key)
        if not b:return await q.answer("Button is disabled.",show_alert=True)
        await q.message.reply_text("👁 <b>Current Preview</b>",reply_markup=safe_markup([[b]]),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d.startswith("a_testbutton_"):
        key=d[len("a_testbutton_"):]
        if key not in BUTTON_DEFAULTS:return ConversationHandler.END
        ok=await premium_test(ctx.bot,q.message.chat_id,key)
        if not ok: await q.answer("Premium icon unavailable; fallback sent.",show_alert=True)
        return ConversationHandler.END
    if d.startswith("a_setemoji_"):
        key=d[len("a_setemoji_"):]
        if key not in BUTTON_DEFAULTS:return ConversationHandler.END
        ctx.user_data["button_edit_key"]=key;return S_BTN_PREMIUM
    if d=="a_premium_test":
        ok=await premium_test(ctx.bot,q.message.chat_id)
        if not ok:await q.answer("Custom emoji unavailable; fallback sent.",show_alert=True)
        return ConversationHandler.END
    if d=="a_members":
        await q.edit_message_text(f"👥 <b>MEMBERS</b>\n\nTotal Users: <b>{scalar('SELECT COUNT(*) FROM users')}</b>",reply_markup=safe_markup([[ib("🔎 Search User","a_search",style="primary",emoji_id=EMOJI["📊"])],[ib("📤 Export Users","a_export",style="success",emoji_id=EMOJI["📌"])],[back_button("a_back")] ]),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d=="a_search":await q.edit_message_text("🔎 Send User ID, username, or name:",reply_markup=back_kb("a_members"));return S_SEARCH
    if d=="a_export":
        p=Path(tempfile.gettempdir())/f"users_{int(time.time())}.csv"
        with db() as c:
            with p.open("w",newline="",encoding="utf-8") as p2:
                w=csv.writer(p2);w.writerow(["user_id","first_name","username","join_date","status"]);w.writerows(c.execute("SELECT user_id,first_name,username,joined_at,status FROM users ORDER BY joined_at"))
        try:
            with p.open("rb") as f:await q.message.reply_document(f,filename=p.name)
        finally:p.unlink(missing_ok=True)
        return ConversationHandler.END
    if d=="a_bcast":
        rows=scalar("SELECT COUNT(*) FROM broadcasts");await q.edit_message_text(f"📣 <b>BROADCAST CENTER</b>\n\nHistory records: <b>{rows}</b>",reply_markup=safe_markup([[ib("📣 New Broadcast","a_newbcast",style="success",emoji_id=EMOJI["📣"])],[back_button("a_back")] ]),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d=="a_newbcast":await q.edit_message_text("📣 <b>Send Text, Photo+Caption, or Video+Caption.</b>",reply_markup=back_kb("a_bcast"),parse_mode=ParseMode.HTML);return S_BCAST
    if d.startswith("a_cancelbc_"):await cancel_bcast(q,d[len("a_cancelbc_"):]);await q.edit_message_text("⏹ Broadcast cancelled.",reply_markup=back_kb("a_bcast"));return ConversationHandler.END
    if d.startswith("a_delbc_"):
        bid=d[len("a_delbc_"):];removed=0
        for uid,mid in bcast_rows(bid):
            try:await ctx.bot.delete_message(uid,mid);removed+=1
            except TelegramError:pass
        with db() as c:c.execute("DELETE FROM broadcast_msgs WHERE bcast_id=?",(bid,));c.execute("DELETE FROM broadcasts WHERE bcast_id=?",(bid,))
        await q.edit_message_text(f"🗑 Broadcast deleted.\nRemoved from <b>{removed}</b> chats.",reply_markup=back_kb("a_bcast"),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d.startswith("a_retrybc_"):
        global BROADCAST_TASK
        bid=d[len("a_retrybc_"):]
        if BROADCAST_LOCK.locked():
            await q.answer("Another broadcast is already running.",show_alert=True)
            return ConversationHandler.END
        with db() as c:
            row=c.execute("SELECT source_chat_id,source_message_id,button_url,button_label,button_style FROM broadcasts WHERE bcast_id=?",(bid,)).fetchone()
            sent_ids={r[0] for r in c.execute("SELECT user_id FROM broadcast_msgs WHERE bcast_id=?",(bid,)).fetchall()}
        if not row:
            await q.answer("Broadcast not found.",show_alert=True);return ConversationHandler.END
        failed_ids=[uid for uid in users() if uid not in sent_ids]
        if not failed_ids:
            await q.answer("No failed recipients found.",show_alert=True);return ConversationHandler.END
        source=SimpleNamespace(chat_id=row[0],message_id=row[1])
        if row[2] and row[3] and row[4] in BUTTON_STYLES:
            source.reply_markup=safe_markup([[ib(row[3],url=row[2],style=row[4])]])
        retry_id=bcast_create(row[0],row[1],"retry",len(failed_ids))
        if row[2] and row[3] and row[4] in BUTTON_STYLES:bcast_set_button(retry_id,row[2],row[3],row[4])
        status_msg=await q.message.reply_text(f"🔁 Retrying <b>{len(failed_ids)}</b> failed recipients...",parse_mode=ParseMode.HTML)
        async def retry_runner():
            async with BROADCAST_LOCK:
                await run_broadcast(ctx.bot,q.message.chat_id,source,retry_id,failed_ids,status_msg)
        BROADCAST_TASK=asyncio.create_task(retry_runner())
        return ConversationHandler.END
    if d=="a_backup_menu":
        names="\n".join("• <code>"+esc(p.name)+"</code>" for p in backup_list()[:10]) or "No backups."
        await q.edit_message_text("💾 <b>BACKUP CENTER</b>\n\n"+names,reply_markup=safe_markup([[ib("💾 Create Backup","a_backup",style="success",emoji_id=EMOJI["⚙️"])],[ib("📤 Download Latest","a_download",style="primary",emoji_id=EMOJI["📌"])],[ib("🗑 Delete Old Backups","a_cleanup",style="danger",emoji_id=EMOJI["❌"])],[back_button("a_back")] ]),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d=="a_backup":
        try:
            await q.answer("💾 Creating backup…")
            p=create_backup()
            with p.open("rb") as f:
                await q.message.reply_document(f,filename=p.name,caption="💾 Backup Ready")
        except Exception as e:
            logger.exception("Backup creation failed")
            await q.answer("❌ Backup failed. Check Render logs.",show_alert=True)
        return ConversationHandler.END
    if d=="a_download":
        ps=backup_list()
        if not ps:return await q.answer("No backups.",show_alert=True)
        with ps[0].open("rb") as f:await q.message.reply_document(f,filename=ps[0].name)
        return ConversationHandler.END
    if d=="a_cleanup":
        await q.edit_message_text(
            "⚠️ <b>Are you sure?</b>\n\nDelete all old backups and keep only the latest one?",
            reply_markup=safe_markup([[
                ib("✅ Confirm","a_cleanup_confirm",style="danger",emoji_id=EMOJI["❌"]),
                ib("❌ Cancel","a_backup_menu",style="primary",emoji_id=EMOJI["📌"])
            ]]), parse_mode=ParseMode.HTML)
        return ConversationHandler.END
    if d=="a_cleanup_confirm":
        for p in backup_list()[1:]:p.unlink(missing_ok=True)
        await q.edit_message_text("🗑 Old backups deleted.",reply_markup=back_kb("a_backup_menu"));return ConversationHandler.END
    if d=="a_restore":
        await q.edit_message_text(
            "⚠️ <b>Are you sure?</b>\n\nRestore will replace the live database after validation. "
            "A safety backup will be created first.",
            reply_markup=safe_markup([[
                ib("✅ Confirm Restore","a_restore_confirm",style="danger",emoji_id=EMOJI["❌"]),
                ib("❌ Cancel","a_back",style="primary",emoji_id=EMOJI["📌"])
            ]]), parse_mode=ParseMode.HTML)
        return ConversationHandler.END
    if d=="a_restore_confirm":
        await q.edit_message_text(
            "♻️ <b>Safe Restore</b>\n\nSend the backup <code>.zip</code> file.\n"
            "ZIP, path traversal, database integrity and required tables are validated.\n"
            "A safety backup is created first.\n\nAfter restore: <b>Restart bot to apply restored state.</b>",
            reply_markup=back_kb("a_backup_menu"), parse_mode=ParseMode.HTML)
        return S_RESTORE
    if d=="a_dbhealth":await q.edit_message_text(dbhealth(),reply_markup=back_kb(),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d=="a_health":await q.edit_message_text(health(),reply_markup=back_kb(),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d=="a_settings":await q.edit_message_text("⚙️ <b>GLOBAL SETTINGS</b>\n\nAuto backup: "+gset("auto_backup_frequency","daily")+" | Keep: "+gset("auto_backup_keep","7"),reply_markup=settings_kb(),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d.startswith("a_toggle_"):
        k=d[len("a_toggle_"):];sset(k,"0" if gset(k,"0")=="1" else "1");await q.edit_message_text("⚙️ Setting updated.",reply_markup=settings_kb());return ConversationHandler.END
    if d=="a_autobackup":sset("auto_backup_frequency","weekly" if gset("auto_backup_frequency","daily")=="daily" else "daily");await q.edit_message_text("⚙️ Auto backup schedule updated.",reply_markup=settings_kb());return ConversationHandler.END
    if d=="a_errors":
        with db() as c:rows=c.execute("SELECT created_at,level,message FROM error_logs ORDER BY id DESC LIMIT 20").fetchall()
        text="📜 <b>RECENT ERRORS</b>\n\n"+"\n".join(f"<code>{esc(r[0])}</code> · <b>{esc(r[1])}</b> · {esc(r[2])}" for r in rows) if rows else "📜 <b>RECENT ERRORS</b>\n\nNo errors."
        await q.edit_message_text(text,reply_markup=safe_markup([[ib("🧹 Clear Logs","a_clearlogs_confirm",style="danger",emoji_id=EMOJI["❌"])],[back_button("a_back")] ]),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d=="a_clearlogs_confirm":await q.edit_message_text("⚠️ <b>Are you sure?</b>",reply_markup=safe_markup([[ib("✅ Confirm","a_clearlogs",style="danger",emoji_id=EMOJI["❌"]),ib("❌ Cancel","a_errors",style="primary",emoji_id=EMOJI["📌"])] ]),parse_mode=ParseMode.HTML);return ConversationHandler.END
    if d=="a_clearlogs":
        with db() as c:c.execute("DELETE FROM error_logs")
        await q.edit_message_text("🧹 Error log cleared.",reply_markup=back_kb());return ConversationHandler.END
    return ConversationHandler.END

async def extra_cb(update,ctx):
    q=update.callback_query
    if not is_admin(q.from_user.id):return await q.answer("❌ Not authorized!",show_alert=True)
    d=q.data
    if d.startswith("a_viewu_"):
        uid=int(d.split("_")[-1])
        with db() as c:r=c.execute("SELECT user_id,first_name,username,joined_at,status FROM users WHERE user_id=?",(uid,)).fetchone()
        if not r:return await q.answer("User not found.",show_alert=True)
        await q.edit_message_text(f"👤 <b>USER</b>\n\nID: <code>{r[0]}</code>\nFirst Name: <b>{esc(r[1])}</b>\nUsername: <b>@{esc(r[2]) if r[2] else '—'}</b>\nJoin Date: <code>{esc(r[3])}</code>\nStatus: <b>{esc(r[4])}</b>",reply_markup=safe_markup([[ib("💬 Send Message",f"a_msgu_{uid}",style="primary",emoji_id=EMOJI["💬"])],[ib("🚫 Block",f"a_blocku_{uid}",style="danger",emoji_id=EMOJI["❌"]),ib("✅ Unblock",f"a_unblocku_{uid}",style="success",emoji_id=EMOJI["✅"])],[ib("🗑 Delete",f"a_deleteu_{uid}",style="danger",emoji_id=EMOJI["❌"])],[back_button("a_members")] ]),parse_mode=ParseMode.HTML)
    elif d.startswith("a_blocku_"):
        uid=int(d.split("_")[-1]);await q.edit_message_text("⚠️ <b>Are you sure?</b>\n\nBlock this user?",reply_markup=safe_markup([[ib("✅ Confirm",f"a_confirmblock_{uid}",style="danger",emoji_id=EMOJI["❌"]),ib("❌ Cancel",f"a_viewu_{uid}",style="primary",emoji_id=EMOJI["📌"])] ]),parse_mode=ParseMode.HTML)
    elif d.startswith("a_confirmblock_"):set_status(int(d.split("_")[-1]),"blocked");await q.edit_message_text("🚫 User blocked.",reply_markup=back_kb("a_members"))
    elif d.startswith("a_unblocku_"):set_status(int(d.split("_")[-1]),"active");await q.edit_message_text("✅ User unblocked.",reply_markup=back_kb("a_members"))
    elif d.startswith("a_deleteu_"):
        uid=int(d.split("_")[-1]);await q.edit_message_text("⚠️ <b>Are you sure?</b>\n\nDelete this user permanently?",reply_markup=safe_markup([[ib("✅ Confirm",f"a_confirmdeleteu_{uid}",style="danger",emoji_id=EMOJI["❌"]),ib("❌ Cancel",f"a_viewu_{uid}",style="primary",emoji_id=EMOJI["📌"])] ]),parse_mode=ParseMode.HTML)
    elif d.startswith("a_confirmdeleteu_"):delete_user(int(d.split("_")[-1]));await q.edit_message_text("🗑 User deleted.",reply_markup=back_kb("a_members"))
    elif d.startswith("a_msgu_"):ctx.user_data["msg_uid"]=int(d.split("_")[-1]);await q.edit_message_text("💬 Send the message to deliver.");return S_USERMSG
    return None

async def auto_backup_loop():
    while True:
        try:
            await asyncio.sleep(3600)
            if gset("auto_backup_enabled","0")=="1":
                last=gset("last_backup","")
                hours=168 if gset("auto_backup_frequency","daily")=="weekly" else 24
                if not last or (datetime.now()-datetime.fromisoformat(last)).total_seconds()>=hours*3600:
                    p=create_backup();cleanup_backups();p.unlink(missing_ok=True)
        except asyncio.CancelledError:return
        except Exception as e:logger.exception("Auto backup: %s",e)

async def _check_force_join_admin_rights(bot):
    rows=channels(False)
    if not rows:return
    try:me=await bot.get_me()
    except TelegramError as e:
        logger.warning("ForceJoin channel admin check failed: %s",e);return
    for r in rows:
        cid=str(r[1]).strip()
        try:
            m=await bot.get_chat_member(cid,me.id)
            status=str(getattr(m,"status","") or "").lower()
            if status not in ("administrator","creator"):
                logger.warning("ForceJoin required channel %s (%s) does not grant the bot admin rights (status=%s). Telegram chat_member updates may not be delivered.",cid,r[2],status)
        except TelegramError as e:
            logger.warning("ForceJoin required channel %s (%s) admin-right check failed: %s",cid,r[2],e)

async def post_init(app):
    global AUTO_BACKUP_TASK
    init_db();await _check_force_join_admin_rights(app.bot);AUTO_BACKUP_TASK=asyncio.create_task(auto_backup_loop())
async def post_shutdown(app):
    global AUTO_BACKUP_TASK,BROADCAST_TASK
    for t in (AUTO_BACKUP_TASK,BROADCAST_TASK):
        if t and not t.done():
            t.cancel()
            try:await t
            except asyncio.CancelledError:pass

async def cancel(u,c):c.user_data.clear();await u.message.reply_text("❌ Cancelled.");return ConversationHandler.END
async def errors(update,ctx):
    global CONFLICT_SHUTDOWN
    err=ctx.error
    if not err:
        return

    # PTB forwards polling errors to the application error handlers with
    # update=None. A Telegram 409 means another process is polling this bot
    # token. Do not keep retrying forever: request a graceful application
    # shutdown from inside the error callback.
    if isinstance(err, telegram.error.Conflict):
        if not CONFLICT_SHUTDOWN:
            CONFLICT_SHUTDOWN=True
            logger.critical(
                "Telegram polling stopped: 409 Conflict detected. "
                "Another process/service is using the same BOT_TOKEN with getUpdates. "
                "This instance will shut down cleanly; stop the other polling instance "
                "or use a newly generated token."
            )
            log_error(
                "CRITICAL",
                "Telegram polling stopped because another getUpdates instance is using the same BOT_TOKEN."
            )
        # PTB documents stop_running() specifically for handlers/error callbacks
        # used with run_polling/run_webhook and it preserves the normal shutdown path.
        try:
            ctx.application.stop_running()
        except Exception:
            logger.exception("Failed to request graceful shutdown after Telegram 409 Conflict")
        return

    logger.exception("Unhandled exception",exc_info=err)
    # Never erase or globally disable saved premium configuration because one
    # button can contain an invalid/unsupported ID. The next explicit render
    # will still consult SQLite, preserving admin configuration.
    msg=str(err).lower()
    if "icon_custom_emoji_id" in msg or "custom emoji" in msg or "not enough rights" in msg:
        log_error("ERROR","Premium custom emoji request rejected; saved configuration preserved: "+str(err))

class RenderHealthHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        if self.path in ("/", "/health", "/healthz"):
            body=("OK\n" if self.path=="/" else "{\"status\":\"ok\"}\n").encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json" if self.path!="/" else "text/plain; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers();self.wfile.write(body);return
        self.send_response(404);self.end_headers()
    def log_message(self,format,*args):
        return

def start_render_health_server():
    global HTTP_SERVER, HTTP_SERVER_THREAD
    port=int(os.getenv("PORT","10000"))
    HTTP_SERVER=ThreadingHTTPServer(("0.0.0.0",port),RenderHealthHandler)
    HTTP_SERVER.daemon_threads=True
    HTTP_SERVER_THREAD=threading.Thread(target=HTTP_SERVER.serve_forever,name="render-health",daemon=True)
    HTTP_SERVER_THREAD.start()
    logger.info("Render health server listening on 0.0.0.0:%s",port)

def stop_render_health_server():
    global HTTP_SERVER
    if HTTP_SERVER is not None:
        try: HTTP_SERVER.shutdown();HTTP_SERVER.server_close()
        except Exception: pass
        HTTP_SERVER=None

def acquire_instance_lock():
    """Prevent duplicate bot processes inside the same OS/container.

    NOTE: This cannot prevent a different Render service, VPS, local machine,
    or other host from polling with the same Telegram BOT_TOKEN. Telegram's
    server-side 409 handler below deals with that external case.
    """
    global INSTANCE_LOCK_FILE, INSTANCE_LOCK_FH
    lock_path = os.getenv("BOT_INSTANCE_LOCK", ".bot-instance.lock")
    INSTANCE_LOCK_FILE = lock_path
    try:
        fh = open(lock_path, "a+", encoding="utf-8")
        if fcntl is None:
            INSTANCE_LOCK_FH = fh
            logger.warning("Local instance lock unavailable on this platform; continuing with Telegram-side conflict protection.")
            return True
        try:
            fcntl.flock(fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            logger.critical("Duplicate bot process detected in this service. Refusing to start a second polling process.")
            fh.close()
            return False
        fh.seek(0)
        fh.truncate()
        fh.write(str(os.getpid()))
        fh.flush()
        os.fsync(fh.fileno())
        INSTANCE_LOCK_FH = fh
        return True
    except Exception as e:
        logger.exception("Unable to acquire bot instance lock: %s", e)
        return False

def release_instance_lock():
    global INSTANCE_LOCK_FH
    if INSTANCE_LOCK_FH:
        try:
            if fcntl is not None:
                fcntl.flock(INSTANCE_LOCK_FH.fileno(), fcntl.LOCK_UN)
        except Exception:
            pass
        try:
            INSTANCE_LOCK_FH.close()
        except Exception:
            pass
        INSTANCE_LOCK_FH = None

def main():
    if not BOT_TOKEN:raise RuntimeError("BOT_TOKEN is missing. Set BOT_TOKEN environment variable.")
    if not ADMIN_ID:raise RuntimeError("ADMIN_ID is missing or invalid. Set ADMIN_ID environment variable.")
    if not acquire_instance_lock():
        raise RuntimeError("A second bot polling process was detected on this service. Stop the duplicate process/service before starting this bot.")
    init_db()
    app=(Application.builder().token(BOT_TOKEN).post_init(post_init).post_shutdown(post_shutdown).build())
    tf=filters.TEXT & ~filters.COMMAND
    bf=(filters.TEXT|filters.PHOTO|filters.VIDEO)&~filters.COMMAND
    rf=filters.Document.ALL&~filters.COMMAND
    conv=ConversationHandler(
      entry_points=[CommandHandler("admin",admin_cmd),CommandHandler("dkboss",dkboss_cmd),CallbackQueryHandler(admin_cb,pattern=r"^a_")],
      states={
        S_CH_ID:[MessageHandler(tf,s_ch_id)],S_CH_NAME:[MessageHandler(tf,s_ch_name)],S_CH_LINK:[MessageHandler(tf,s_ch_link)],
        S_WELCOME:[MessageHandler(tf,s_welcome)],S_WELCOME_PHOTO:[MessageHandler((filters.PHOTO|filters.TEXT)&~filters.COMMAND,s_photo)],
        S_POSTJOIN:[MessageHandler(tf,s_postjoin)],S_TOP:[MessageHandler(tf,s_top)],S_BTN1:[MessageHandler(tf,s_btn1)],S_BTN2:[MessageHandler(tf,s_btn2)],S_BTN3:[MessageHandler(tf,s_btn3)],
        S_BCAST:[MessageHandler(bf,start_bcast)],S_BCAST_BTN_ASK:[CallbackQueryHandler(bcast_btn_ask,pattern=r"^bcast_btn_(yes|skip|cancel)$")],S_BCAST_BTN_LINK:[MessageHandler(tf,bcast_btn_link)],S_BCAST_BTN_NAME:[MessageHandler(tf,bcast_btn_name)],S_BCAST_BTN_STYLE:[CallbackQueryHandler(bcast_btn_style,pattern=r"^(bcast_style_|bcast_btn_cancel)")],S_BCAST_PREVIEW:[CallbackQueryHandler(bcast_preview,pattern=r"^bcast_(confirm|cancel)$")],S_RESTORE:[MessageHandler(rf,s_restore)],S_SEARCH:[MessageHandler(tf,s_search)],S_USERMSG:[MessageHandler(bf,s_usermsg)],
        S_EDITNAME:[MessageHandler(tf,s_editname)],S_EDITLINK:[MessageHandler(tf,s_editlink)],S_EMOJI:[MessageHandler(tf,s_emoji)],S_BTN_NAME:[MessageHandler(tf,s_button_name)],S_BTN_NORMAL:[MessageHandler(tf,s_button_normal)],S_BTN_PREMIUM:[MessageHandler(tf,s_button_premium)],S_FORCE_JOIN_MSG:[MessageHandler(tf,s_force_join_message)]
      },fallbacks=[CommandHandler("cancel",cancel),CallbackQueryHandler(admin_cb,pattern=r"^a_")],per_chat=False,per_user=True,allow_reentry=True)
    app.add_handler(CommandHandler("start",start));app.add_handler(conv)
    app.add_handler(CallbackQueryHandler(cb_check,pattern=r"^check_joined$"));app.add_handler(CallbackQueryHandler(cb_btn,pattern=r"^btn[123]$"));app.add_handler(CallbackQueryHandler(cb_back,pattern=r"^back_main$"))
    app.add_handler(ChatJoinRequestHandler(join_request))
    app.add_handler(ChatMemberHandler(chat_member_update,ChatMemberHandler.CHAT_MEMBER))
    app.add_error_handler(errors)
    start_render_health_server()
    logger.info("Bot started: v%s / PTB %s / ADMIN_ID=%s / OWNER_ID=%s",BOT_VERSION,telegram.__version__,ADMIN_ID,OWNER_ID)
    try:
        # Exactly one polling owner for this process. Telegram 409 conflicts are
        # handled by the registered error handler via Application.stop_running(),
        # which lets PTB complete its documented graceful shutdown sequence.
        app.run_polling(
            allowed_updates=Update.ALL_TYPES,
            drop_pending_updates=True,
        )
    finally:
        stop_render_health_server()
        release_instance_lock()
    if CONFLICT_SHUTDOWN:
        # A detected 409 is a real deployment/runtime conflict, so make Render
        # restart the service instead of leaving a conflicted process alive.
        raise SystemExit(1)

if __name__=="__main__":main()
