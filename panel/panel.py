#!/usr/bin/env python3
import os
import sys
import json
import time
import subprocess
import secrets
import hashlib
import threading
import re
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from http import cookies
from urllib.parse import urlparse, parse_qs
from datetime import datetime, timedelta

# --- CONSTANTS ---
DB_FILE = "/etc/firewallfalcon/users.db"
RESELLERS_DB = "/etc/firewallfalcon/resellers.db"
BW_DIR = "/etc/firewallfalcon/bandwidth"
PANEL_CONF = "/etc/firewallfalcon/panel.conf"
PANEL_HTML = "/etc/firewallfalcon/panel/index.html"
FF_USERS_GROUP = "firewallfalcon-users"
PORT = 44380

# --- GLOBAL STATE ---
sessions = {}  # token -> {"username": str, "role": "admin"|"reseller", "created_at": float}
db_lock = threading.Lock()

PROTOCOLS = [
    {"name": "OpenSSH", "service": "sshd", "service_alt": "ssh", "check_file": None, "port": "22"},
    {"name": "BadVPN (UDPGW)", "service": "badvpn", "check_file": "/etc/systemd/system/badvpn.service", "port": "7300"},
    {"name": "UDP Custom", "service": "udp-custom", "check_file": "/etc/systemd/system/udp-custom.service", "port": "36712"},
    {"name": "HAProxy Edge", "service": "haproxy", "check_file": "/etc/haproxy/haproxy.cfg", "port": "80/443"},
    {"name": "Nginx Proxy", "service": "nginx", "check_file": "/etc/nginx/sites-available/default", "port": "8880/8443"},
    {"name": "DNSTT (SlowDNS)", "service": "dnstt", "check_file": "/etc/systemd/system/dnstt.service", "port": "53"},
    {"name": "Falcon Proxy", "service": "falconproxy", "check_file": "/etc/systemd/system/falconproxy.service", "port": "8080"},
    {"name": "ZiVPN", "service": "zivpn", "check_file": "/etc/systemd/system/zivpn.service", "port": "5667"},
    {"name": "X-UI / 3X-UI", "service": "x-ui", "check_file": "/etc/systemd/system/x-ui.service", "port": "2053"},
]

# --- UTILS ---
def run_cmd(cmd_args, ignore_errors=False):
    try:
        if isinstance(cmd_args, str):
            res = subprocess.run(cmd_args, shell=True, capture_output=True, text=True, timeout=10)
        else:
            res = subprocess.run(cmd_args, capture_output=True, text=True, timeout=10)
        if not ignore_errors and res.returncode != 0:
            print(f"Command error: {cmd_args} -> {res.stderr}", file=sys.stderr)
        return res.returncode, res.stdout.strip(), res.stderr.strip()
    except Exception as e:
        print(f"Exception running command {cmd_args}: {e}", file=sys.stderr)
        return -1, "", str(e)

# --- USERS DB ---
def parse_db_line(line):
    parts = line.strip().split(":")
    if len(parts) < 5:
        return None
    user = {
        "username": parts[0],
        "password": parts[1],
        "expire_date": parts[2],
        "conn_limit": int(parts[3]) if parts[3].isdigit() else 1,
        "bandwidth_gb": float(parts[4]),
        "daily_bandwidth_gb": 0.0,
        "account_type": "",
        "owner": "admin"
    }
    if len(parts) > 5:
        try:
            user["daily_bandwidth_gb"] = float(parts[5])
        except ValueError:
            user["daily_bandwidth_gb"] = 0.0
    if len(parts) > 6:
        user["account_type"] = parts[6]
    if len(parts) > 7:
        user["owner"] = parts[7] if parts[7] else "admin"
    return user

def read_db():
    users = []
    if not os.path.exists(DB_FILE):
        return users
    with open(DB_FILE, "r") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            u = parse_db_line(line)
            if u:
                users.append(u)
    return users

def _fmt_bw(v):
    """Format bandwidth: 0.0 -> '0', 3.5 -> '3.5', 10.0 -> '10'"""
    f = float(v)
    return str(int(f)) if f == int(f) else str(f)

def format_db_line(u):
    bw = _fmt_bw(u.get('bandwidth_gb', 0))
    dbw = _fmt_bw(u.get('daily_bandwidth_gb', 0))
    owner = u.get('owner', 'admin')
    return f"{u['username']}:{u['password']}:{u['expire_date']}:{u['conn_limit']}:{bw}:{dbw}:{u.get('account_type','web')}:{owner}\n"

# --- RESELLERS DB ---
def parse_reseller_line(line):
    parts = line.strip().split(":")
    if len(parts) < 5:
        return None
    return {
        "username": parts[0],
        "password": parts[1],
        "expire_date": parts[2],
        "max_users": int(parts[3]) if parts[3].isdigit() else 10,
        "enabled": parts[4] == "1"
    }

def read_resellers():
    resellers = []
    if not os.path.exists(RESELLERS_DB):
        return resellers
    with open(RESELLERS_DB, "r") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            r = parse_reseller_line(line)
            if r:
                resellers.append(r)
    return resellers

def format_reseller_line(r):
    enabled = "1" if r.get("enabled", True) else "0"
    return f"{r['username']}:{r['password']}:{r['expire_date']}:{r['max_users']}:{enabled}\n"

def write_resellers(resellers):
    os.makedirs(os.path.dirname(RESELLERS_DB), exist_ok=True)
    with open(RESELLERS_DB, "w") as f:
        for r in resellers:
            f.write(format_reseller_line(r))

# --- ONLINE SESSIONS ---
def get_online_sessions(target_user=None):
    managed_users = set(u["username"] for u in read_db())
    if target_user and target_user not in managed_users:
        return 0
    
    user_pids = {}
    try:
        code, out, _ = run_cmd(["ps", "-C", "sshd,sshd-session", "-o", "pid=,user="], ignore_errors=True)
        if code == 0 and out:
            for line in out.strip().splitlines():
                parts = line.split()
                if len(parts) != 2:
                    continue
                pid, owner = parts
                if owner in ("root", "sshd", ""):
                    continue
                if owner not in managed_users:
                    continue
                if target_user and owner != target_user:
                    continue
                if owner not in user_pids:
                    user_pids[owner] = set()
                user_pids[owner].add(pid)
    except Exception as e:
        print(f"Error checking online sessions: {e}", file=sys.stderr)
        
    if target_user:
        return len(user_pids.get(target_user, set()))
    else:
        return sum(len(pids) for pids in user_pids.values())

def get_online_sessions_for_users(usernames):
    """Get online session counts for a set of usernames efficiently (single ps call)."""
    user_pids = {}
    try:
        code, out, _ = run_cmd(["ps", "-C", "sshd,sshd-session", "-o", "pid=,user="], ignore_errors=True)
        if code == 0 and out:
            for line in out.strip().splitlines():
                parts = line.split()
                if len(parts) != 2:
                    continue
                pid, owner = parts
                if owner in ("root", "sshd", ""):
                    continue
                if owner not in usernames:
                    continue
                if owner not in user_pids:
                    user_pids[owner] = set()
                user_pids[owner].add(pid)
    except Exception as e:
        print(f"Error checking online sessions: {e}", file=sys.stderr)
    return user_pids

def read_file_int(path, default=0):
    try:
        if os.path.exists(path):
            with open(path, "r") as f:
                return int(f.read().strip())
    except Exception:
        pass
    return default

# --- PANEL CREDS ---
def get_panel_creds():
    creds = {"PANEL_USER": "", "PANEL_PASS_HASH": "", "PANEL_PASS_PLAIN": "", "PANEL_SECRET": ""}
    if os.path.exists(PANEL_CONF):
        with open(PANEL_CONF, "r") as f:
            for line in f:
                line = line.strip()
                if "=" in line:
                    k, v = line.split("=", 1)
                    v = v.strip().strip('"').strip("'")
                    if k in creds:
                        creds[k] = v
    return creds

def write_panel_creds(user, pass_plain, secret=None):
    creds = get_panel_creds()
    creds["PANEL_USER"] = user
    creds["PANEL_PASS_PLAIN"] = pass_plain
    creds["PANEL_PASS_HASH"] = hashlib.sha256(pass_plain.encode()).hexdigest()
    if secret is not None:
        creds["PANEL_SECRET"] = secret.strip().lstrip('/')
    
    os.makedirs(os.path.dirname(PANEL_CONF), exist_ok=True)
    with open(PANEL_CONF, "w") as f:
        for k, v in creds.items():
            f.write(f"{k}={v}\n")

# --- SESSION ---
def cleanup_sessions():
    now = time.time()
    expired = [t for t, s in sessions.items() if now - s["created_at"] > 86400]
    for t in expired:
        del sessions[t]

def generate_password(length=8):
    chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    return "".join(secrets.choice(chars) for _ in range(length))

def calculate_expire_date(days):
    return (datetime.now() + timedelta(days=days)).strftime("%Y-%m-%d")

def check_session(headers):
    """Returns session info dict or None if not authenticated."""
    cleanup_sessions()
    if "Cookie" in headers:
        C = cookies.SimpleCookie(headers["Cookie"])
        if "session" in C:
            token = C["session"].value
            if token in sessions:
                return sessions[token]
    return None

# --- HTTP HANDLER ---
class PanelAPIHandler(BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        pass  # Suppress default logging

    def send_json(self, status, data, extra_headers=None):
        self.send_response(status)
        self.send_header('Content-Type', 'application/json')
        if extra_headers:
            for k, v in extra_headers.items():
                self.send_header(k, v)
        self.end_headers()
        self.wfile.write(json.dumps(data).encode('utf-8'))

    def _get_session(self):
        """Helper: returns session dict or sends 401 and returns None."""
        s = check_session(self.headers)
        if not s:
            self.send_json(401, {"error": "Unauthorized"})
        return s

    def _require_admin(self, session):
        """Helper: returns True if admin, else sends 403 and returns False."""
        if session.get("role") != "admin":
            self.send_json(403, {"error": "Admin access required"})
            return False
        return True

    def do_GET(self):
        try:
            parsed_path = urlparse(self.path)
            raw_path = parsed_path.path.strip()
            creds = get_panel_creds()
            secret = creds.get("PANEL_SECRET", "").strip().lstrip('/')
            
            # Check secret path matching for HTML serving
            is_html_request = False
            if not secret:
                if raw_path in ("/", "/index.html"):
                    is_html_request = True
            else:
                valid_paths = (f"/{secret}", f"/{secret}/", f"/{secret}/index.html")
                if raw_path in valid_paths:
                    is_html_request = True

            if is_html_request:
                if os.path.exists(PANEL_HTML):
                    with open(PANEL_HTML, "rb") as f:
                        content = f.read()
                    self.send_response(200)
                    self.send_header('Content-Type', 'text/html')
                    self.end_headers()
                    self.wfile.write(content)
                else:
                    self.send_response(404)
                    self.end_headers()
                    self.wfile.write(b"HTML not found")
                return

            # Clean API path if prefixed with secret
            api_path = raw_path
            if secret and api_path.startswith(f"/{secret}/api/"):
                api_path = api_path[len(secret) + 1:]
            
            if not api_path.startswith("/api/"):
                self.send_response(404)
                self.end_headers()
                self.wfile.write(b"Not Found")
                return

            session = self._get_session()
            if not session:
                return

            if api_path == "/api/me":
                self.handle_get_me(session)
            elif api_path == "/api/dashboard":
                self.handle_get_dashboard(session)
            elif api_path == "/api/users":
                self.handle_get_users(session)
            elif api_path == "/api/protocols":
                if not self._require_admin(session):
                    return
                self.handle_get_protocols()
            elif api_path == "/api/settings":
                if not self._require_admin(session):
                    return
                self.handle_get_settings()
            elif api_path == "/api/resellers":
                if not self._require_admin(session):
                    return
                self.handle_get_resellers()
            else:
                self.send_json(404, {"error": "Not Found"})
        except Exception as e:
            print(f"Error handling GET {self.path}: {e}", file=sys.stderr)
            self.send_json(500, {"error": str(e)})

    def do_POST(self):
        parsed_path = urlparse(self.path)
        path = parsed_path.path
        
        content_length = int(self.headers.get('Content-Length', 0))
        post_data = self.rfile.read(content_length)
        try:
            body = json.loads(post_data.decode('utf-8')) if post_data else {}
        except json.JSONDecodeError:
            body = {}

        if path == "/api/login":
            self.handle_login(body)
            return

        session = self._get_session()
        if not session:
            return

        if path == "/api/logout":
            self.handle_logout()
        elif path == "/api/users":
            self.handle_post_users(body, session)
        elif path == "/api/users/bulk":
            self.handle_post_users_bulk(body, session)
        elif path.startswith("/api/users/") and path.endswith("/lock"):
            user = path.split("/")[3]
            self.handle_user_action(user, "lock", session=session)
        elif path.startswith("/api/users/") and path.endswith("/unlock"):
            user = path.split("/")[3]
            self.handle_user_action(user, "unlock", session=session)
        elif path.startswith("/api/users/") and path.endswith("/renew"):
            user = path.split("/")[3]
            self.handle_user_action(user, "renew", body=body, session=session)
        elif path.startswith("/api/users/") and path.endswith("/reset-bandwidth"):
            user = path.split("/")[3]
            self.handle_user_action(user, "reset-bandwidth", session=session)
        elif path.startswith("/api/protocols/") and path.endswith("/restart"):
            if not self._require_admin(session):
                return
            service = path.split("/")[3]
            self.handle_protocol_restart(service)
        elif path == "/api/resellers":
            if not self._require_admin(session):
                return
            self.handle_post_reseller(body)
        elif path.startswith("/api/resellers/") and path.endswith("/toggle"):
            if not self._require_admin(session):
                return
            reseller_name = path.split("/")[3]
            self.handle_toggle_reseller(reseller_name)
        else:
            self.send_json(404, {"error": "Not Found"})

    def do_PUT(self):
        parsed_path = urlparse(self.path)
        path = parsed_path.path
        
        session = self._get_session()
        if not session:
            return

        content_length = int(self.headers.get('Content-Length', 0))
        post_data = self.rfile.read(content_length)
        try:
            body = json.loads(post_data.decode('utf-8')) if post_data else {}
        except json.JSONDecodeError:
            body = {}

        if path.startswith("/api/users/"):
            user = path.split("/")[3]
            self.handle_put_user(user, body, session)
        elif path == "/api/settings":
            if not self._require_admin(session):
                return
            self.handle_put_settings(body)
        elif path.startswith("/api/resellers/"):
            if not self._require_admin(session):
                return
            reseller_name = path.split("/")[3]
            self.handle_put_reseller(reseller_name, body)
        else:
            self.send_json(404, {"error": "Not Found"})

    def do_DELETE(self):
        parsed_path = urlparse(self.path)
        path = parsed_path.path
        
        session = self._get_session()
        if not session:
            return

        if path.startswith("/api/resellers/"):
            if not self._require_admin(session):
                return
            reseller_name = path.split("/")[3]
            # Check query params for delete_users flag
            qs = parse_qs(urlparse(self.path).query)
            delete_users = qs.get("delete_users", ["0"])[0] == "1"
            self.handle_delete_reseller(reseller_name, delete_users)
        elif path.startswith("/api/users/"):
            user = path.split("/")[3]
            self.handle_delete_user(user, session)
        else:
            self.send_json(404, {"error": "Not Found"})

    # --- OWNERSHIP CHECK ---
    def _check_user_ownership(self, username, session):
        """Check if the session owner can manage this user. Returns True if allowed."""
        if session.get("role") == "admin":
            return True
        # Reseller can only manage their own users
        users = read_db()
        user = next((u for u in users if u["username"] == username), None)
        if not user:
            return False
        return user.get("owner", "admin") == session.get("username")

    # --- HANDLERS ---
    def handle_login(self, body):
        user = body.get("username", "")
        pwd = body.get("password", "")
        pwd_hash = hashlib.sha256(pwd.encode()).hexdigest()
        
        # Check admin credentials first
        creds = get_panel_creds()
        if user == creds.get("PANEL_USER") and pwd_hash == creds.get("PANEL_PASS_HASH"):
            token = secrets.token_hex(32)
            sessions[token] = {"username": user, "role": "admin", "created_at": time.time()}
            cookie_str = f"session={token}; Path=/; HttpOnly; Max-Age=86400"
            self.send_json(200, {"success": True, "role": "admin"}, {"Set-Cookie": cookie_str})
            return

        # Check reseller credentials
        resellers = read_resellers()
        for r in resellers:
            if r["username"] == user and r["password"] == pwd:
                if not r["enabled"]:
                    return self.send_json(401, {"error": "Account is disabled"})
                # Check reseller expiry
                try:
                    exp = datetime.strptime(r["expire_date"], "%Y-%m-%d")
                    if exp < datetime.now():
                        return self.send_json(401, {"error": "Account has expired"})
                except ValueError:
                    pass
                token = secrets.token_hex(32)
                sessions[token] = {"username": user, "role": "reseller", "created_at": time.time()}
                cookie_str = f"session={token}; Path=/; HttpOnly; Max-Age=86400"
                self.send_json(200, {"success": True, "role": "reseller"}, {"Set-Cookie": cookie_str})
                return

        self.send_json(401, {"error": "Invalid credentials"})

    def handle_logout(self):
        if "Cookie" in self.headers:
            C = cookies.SimpleCookie(self.headers["Cookie"])
            if "session" in C:
                token = C["session"].value
                if token in sessions:
                    del sessions[token]
        cookie_str = f"session=; Path=/; HttpOnly; Max-Age=0"
        self.send_json(200, {"success": True}, {"Set-Cookie": cookie_str})

    def handle_get_me(self, session):
        data = {"role": session.get("role", "admin"), "username": session.get("username", "")}
        if session.get("role") == "reseller":
            resellers = read_resellers()
            r = next((x for x in resellers if x["username"] == session["username"]), None)
            if r:
                data["expire_date"] = r["expire_date"]
                data["max_users"] = r["max_users"]
                # Count users owned by this reseller
                users = read_db()
                owned = [u for u in users if u.get("owner") == session["username"]]
                data["created_users"] = len(owned)
        self.send_json(200, data)

    def handle_get_dashboard(self, session):
        _, ip, _ = run_cmd("curl -s -4 --max-time 3 icanhazip.com")
        
        os_name = "Unknown OS"
        try:
            with open("/etc/os-release") as f:
                for line in f:
                    if line.startswith("PRETTY_NAME="):
                        os_name = line.split("=")[1].strip().strip('"')
                        break
        except Exception:
            pass

        _, uptime_str, _ = run_cmd("uptime -p")
        if uptime_str.startswith("up "):
            uptime_str = uptime_str[3:]

        ram_total = 0
        ram_available = 0
        try:
            with open("/proc/meminfo") as f:
                for line in f:
                    if line.startswith("MemTotal:"):
                        ram_total = int(line.split()[1]) // 1024
                    elif line.startswith("MemAvailable:"):
                        ram_available = int(line.split()[1]) // 1024
        except Exception:
            pass
        ram_used = ram_total - ram_available if ram_total > 0 else 0
        ram_percent = round((ram_used / ram_total) * 100, 1) if ram_total > 0 else 0.0

        cpu_load = 0.0
        try:
            with open("/proc/loadavg") as f:
                cpu_load = float(f.read().split()[0])
        except Exception:
            pass

        users = read_db()

        if session.get("role") == "reseller":
            # Reseller sees only their stats
            owned_users = [u for u in users if u.get("owner") == session["username"]]
            owned_usernames = set(u["username"] for u in owned_users)
            online_pids = get_online_sessions_for_users(owned_usernames)
            online_total = sum(len(pids) for pids in online_pids.values())
            
            resellers = read_resellers()
            r = next((x for x in resellers if x["username"] == session["username"]), None)
            max_users = r["max_users"] if r else 0
            expire_date = r["expire_date"] if r else "N/A"

            self.send_json(200, {
                "server_ip": ip,
                "os_name": os_name,
                "uptime": uptime_str,
                "ram_percent": ram_percent,
                "ram_used_mb": ram_used,
                "ram_total_mb": ram_total,
                "cpu_load_1m": cpu_load,
                "user_count": len(owned_users),
                "online_sessions": online_total,
                "protocols": [],
                "reseller_info": {
                    "max_users": max_users,
                    "created_users": len(owned_users),
                    "expire_date": expire_date
                }
            })
        else:
            # Admin sees everything
            online_sessions = get_online_sessions()
            procs = self.get_protocols_status()
            self.send_json(200, {
                "server_ip": ip,
                "os_name": os_name,
                "uptime": uptime_str,
                "ram_percent": ram_percent,
                "ram_used_mb": ram_used,
                "ram_total_mb": ram_total,
                "cpu_load_1m": cpu_load,
                "user_count": len(users),
                "online_sessions": online_sessions,
                "protocols": procs
            })

    def get_protocols_status(self):
        procs = []
        for p in PROTOCOLS:
            installed = False
            if p["check_file"] is None:
                installed = True
            else:
                installed = os.path.exists(p["check_file"])
                
            running = False
            if installed:
                code, _, _ = run_cmd(["systemctl", "is-active", p["service"]])
                if code == 0:
                    running = True
                elif "service_alt" in p:
                    code2, _, _ = run_cmd(["systemctl", "is-active", p["service_alt"]])
                    if code2 == 0:
                        running = True
                        
            procs.append({
                "name": p["name"],
                "service": p["service"],
                "installed": installed,
                "running": running,
                "port": p["port"]
            })
        return procs

    def handle_get_users(self, session):
        users = read_db()
        
        # Scope by role
        if session.get("role") == "reseller":
            users = [u for u in users if u.get("owner") == session["username"]]

        # Efficient batch online session lookup
        all_usernames = set(u["username"] for u in users)
        online_pids = get_online_sessions_for_users(all_usernames)

        result = []
        for u in users:
            un = u["username"]
            total_bw = read_file_int(f"{BW_DIR}/{un}.usage")
            daily_bw = read_file_int(f"{BW_DIR}/{un}.daily_usage")
            
            code, out, _ = run_cmd(["passwd", "-S", un])
            is_locked = False
            if code == 0 and len(out.split()) >= 2:
                is_locked = (out.split()[1] == "L")
                
            code2, _, _ = run_cmd(["id", un])
            exists_on_system = (code2 == 0)
            
            is_expired = False
            try:
                if u["expire_date"] != "Never" and u["expire_date"]:
                    exp_date = datetime.strptime(u["expire_date"], "%Y-%m-%d")
                    is_expired = exp_date < datetime.now()
            except ValueError:
                pass
            
            online_count = len(online_pids.get(un, set()))
            
            u_ext = dict(u)
            u_ext["total_used_bytes"] = total_bw
            u_ext["daily_used_bytes"] = daily_bw
            u_ext["is_locked"] = is_locked
            u_ext["is_expired"] = is_expired
            u_ext["is_online"] = online_count > 0
            u_ext["online_sessions"] = online_count
            u_ext["exists_on_system"] = exists_on_system
            
            result.append(u_ext)
            
        self.send_json(200, {"users": result})

    def _create_user(self, un, pwd, days, conn, bw, dbw, acct_type="web", owner="admin"):
        if not re.match(r'^[a-zA-Z0-9_]{3,32}$', un):
            raise ValueError("Invalid username")
            
        if any(u["username"] == un for u in read_db()):
            raise ValueError("User already exists in DB")
            
        code, _, _ = run_cmd(["id", un])
        if code == 0:
            raise ValueError("User already exists on system")

        run_cmd(["useradd", "-m", "-s", "/usr/sbin/nologin", un])
        run_cmd(["usermod", "-aG", FF_USERS_GROUP, un], ignore_errors=True)
        run_cmd(f"echo '{un}:{pwd}' | chpasswd")
        
        exp_date_str = calculate_expire_date(days)
        run_cmd(["chage", "-E", exp_date_str, un])
        
        new_u = {
            "username": un,
            "password": pwd,
            "expire_date": exp_date_str,
            "conn_limit": conn,
            "bandwidth_gb": bw,
            "daily_bandwidth_gb": dbw,
            "account_type": acct_type,
            "owner": owner
        }
        
        with db_lock:
            os.makedirs(os.path.dirname(DB_FILE), exist_ok=True)
            with open(DB_FILE, "a") as f:
                f.write(format_db_line(new_u))
                
        return new_u

    def handle_post_users(self, body, session):
        try:
            owner = session.get("username", "admin") if session.get("role") == "reseller" else "admin"

            # Reseller quota check
            if session.get("role") == "reseller":
                resellers = read_resellers()
                r = next((x for x in resellers if x["username"] == session["username"]), None)
                if not r:
                    return self.send_json(403, {"error": "Reseller account not found"})
                users = read_db()
                owned = [u for u in users if u.get("owner") == session["username"]]
                if len(owned) >= r["max_users"]:
                    return self.send_json(403, {"error": f"User limit reached ({r['max_users']})"})

            un = body.get("username", "")
            pwd = body.get("password", "") or generate_password()
            days = int(body.get("days", 30))
            conn = int(body.get("conn_limit", 1))
            bw = float(body.get("bandwidth_gb", 0))
            dbw = float(body.get("daily_bandwidth_gb", 0))
            
            new_u = self._create_user(un, pwd, days, conn, bw, dbw, owner=owner)
            self.send_json(200, new_u)
        except Exception as e:
            self.send_json(400, {"error": str(e)})

    def handle_post_users_bulk(self, body, session):
        try:
            owner = session.get("username", "admin") if session.get("role") == "reseller" else "admin"
            
            # Reseller quota check
            remaining_quota = float('inf')
            if session.get("role") == "reseller":
                resellers = read_resellers()
                r = next((x for x in resellers if x["username"] == session["username"]), None)
                if not r:
                    return self.send_json(403, {"error": "Reseller account not found"})
                users = read_db()
                owned = [u for u in users if u.get("owner") == session["username"]]
                remaining_quota = r["max_users"] - len(owned)
                if remaining_quota <= 0:
                    return self.send_json(403, {"error": f"User limit reached ({r['max_users']})"})

            prefix = body.get("prefix", "user")
            count = min(int(body.get("count", 1)), int(remaining_quota))
            days = int(body.get("days", 30))
            conn = int(body.get("conn_limit", 1))
            bw = float(body.get("bandwidth_gb", 0))
            dbw = float(body.get("daily_bandwidth_gb", 0))
            
            created = []
            existing_users = set(u["username"] for u in read_db())
            
            idx = 1
            for _ in range(count):
                while f"{prefix}{idx}" in existing_users:
                    idx += 1
                un = f"{prefix}{idx}"
                pwd = generate_password()
                
                try:
                    u = self._create_user(un, pwd, days, conn, bw, dbw, "bulk", owner=owner)
                    created.append(u)
                    existing_users.add(un)
                except Exception as e:
                    pass # skip failures in bulk
                idx += 1
                
            self.send_json(200, {"users": created})
        except Exception as e:
            self.send_json(400, {"error": str(e)})

    def handle_put_user(self, username, body, session):
        if not self._check_user_ownership(username, session):
            return self.send_json(403, {"error": "Access denied"})

        with db_lock:
            users = read_db()
            idx = next((i for i, u in enumerate(users) if u["username"] == username), -1)
            if idx == -1:
                return self.send_json(404, {"error": "User not found"})
                
            u = users[idx]
            
            if "password" in body:
                u["password"] = body["password"]
                run_cmd(f"echo '{username}:{u['password']}' | chpasswd")
                
            if "days" in body:
                u["expire_date"] = calculate_expire_date(int(body["days"]))
                run_cmd(["chage", "-E", u["expire_date"], username])
                
            if "conn_limit" in body:
                u["conn_limit"] = int(body["conn_limit"])
                
            if "bandwidth_gb" in body:
                u["bandwidth_gb"] = float(body["bandwidth_gb"])
                
            if "daily_bandwidth_gb" in body:
                u["daily_bandwidth_gb"] = float(body["daily_bandwidth_gb"])

            lines = []
            with open(DB_FILE, "r") as f:
                lines = f.readlines()
                
            with open(DB_FILE, "w") as f:
                for line in lines:
                    if line.startswith(f"{username}:"):
                        f.write(format_db_line(u))
                    else:
                        f.write(line)
                        
            self.send_json(200, u)

    def handle_delete_user(self, username, session):
        if not self._check_user_ownership(username, session):
            return self.send_json(403, {"error": "Access denied"})

        run_cmd(["killall", "-u", username, "-9"], ignore_errors=True)
        run_cmd(["userdel", "-r", username], ignore_errors=True)
        
        with db_lock:
            lines = []
            if os.path.exists(DB_FILE):
                with open(DB_FILE, "r") as f:
                    lines = f.readlines()
                with open(DB_FILE, "w") as f:
                    for line in lines:
                        if not line.startswith(f"{username}:"):
                            f.write(line)
                            
        run_cmd(f"rm -f {BW_DIR}/{username}.*", ignore_errors=True)
        run_cmd(f"rm -f /etc/firewallfalcon/banners/{username}.txt", ignore_errors=True)
        
        self.send_json(200, {"success": True})

    def handle_user_action(self, username, action, body=None, session=None):
        if not self._check_user_ownership(username, session):
            return self.send_json(403, {"error": "Access denied"})

        if action == "lock":
            run_cmd(["usermod", "-L", username])
            run_cmd(["killall", "-u", username, "-9"], ignore_errors=True)
            self.send_json(200, {"success": True})
            
        elif action == "unlock":
            run_cmd(["usermod", "-U", username])
            run_cmd(f"rm -f {BW_DIR}/{username}.conn_locked", ignore_errors=True)
            run_cmd(f"rm -f {BW_DIR}/{username}.daily_locked", ignore_errors=True)
            self.send_json(200, {"success": True})
            
        elif action == "renew":
            days = int(body.get("days", 30)) if body else 30
            with db_lock:
                users = read_db()
                u = next((x for x in users if x["username"] == username), None)
                if not u:
                    return self.send_json(404, {"error": "User not found"})
                u["expire_date"] = calculate_expire_date(days)
                run_cmd(["chage", "-E", u["expire_date"], username])
                
                lines = []
                with open(DB_FILE, "r") as f:
                    lines = f.readlines()
                with open(DB_FILE, "w") as f:
                    for line in lines:
                        if line.startswith(f"{username}:"):
                            f.write(format_db_line(u))
                        else:
                            f.write(line)
            self.send_json(200, {"success": True, "expire_date": u["expire_date"]})
            
        elif action == "reset-bandwidth":
            os.makedirs(BW_DIR, exist_ok=True)
            with open(f"{BW_DIR}/{username}.usage", "w") as f:
                f.write("0")
            with open(f"{BW_DIR}/{username}.daily_usage", "w") as f:
                f.write("0")
            run_cmd(f"rm -f {BW_DIR}/{username}.conn_locked", ignore_errors=True)
            run_cmd(f"rm -f {BW_DIR}/{username}.daily_locked", ignore_errors=True)
            run_cmd(["usermod", "-U", username])
            self.send_json(200, {"success": True})
            
        else:
            self.send_json(400, {"error": "Unknown action"})

    def handle_get_protocols(self):
        self.send_json(200, self.get_protocols_status())

    def handle_protocol_restart(self, service):
        code, out, err = run_cmd(["systemctl", "restart", service])
        if code == 0:
            self.send_json(200, {"success": True})
        else:
            self.send_json(500, {"success": False, "error": err})

    def handle_get_settings(self):
        creds = get_panel_creds()
        self.send_json(200, {
            "username": creds.get("PANEL_USER", ""),
            "secret": creds.get("PANEL_SECRET", "")
        })

    def handle_put_settings(self, body):
        creds = get_panel_creds()
        curr_pwd = body.get("current_password", "")
        new_user = body.get("new_username", "").strip() or creds.get("PANEL_USER", "")
        new_pwd = body.get("new_password", "").strip() or creds.get("PANEL_PASS_PLAIN", "")
        new_secret = body.get("new_secret", "").strip().lstrip('/')
        
        curr_hash = hashlib.sha256(curr_pwd.encode()).hexdigest()
        if curr_hash != creds.get("PANEL_PASS_HASH"):
            return self.send_json(401, {"error": "Invalid current password"})
            
        write_panel_creds(new_user, new_pwd, secret=new_secret)
        self.send_json(200, {"success": True, "secret": new_secret})

    # --- RESELLER HANDLERS (admin only) ---
    def handle_get_resellers(self):
        resellers = read_resellers()
        users = read_db()
        result = []
        for r in resellers:
            owned = [u for u in users if u.get("owner") == r["username"]]
            is_expired = False
            try:
                exp = datetime.strptime(r["expire_date"], "%Y-%m-%d")
                is_expired = exp < datetime.now()
            except ValueError:
                pass
            result.append({
                "username": r["username"],
                "password": r["password"],
                "expire_date": r["expire_date"],
                "max_users": r["max_users"],
                "created_users": len(owned),
                "enabled": r["enabled"],
                "is_expired": is_expired
            })
        self.send_json(200, {"resellers": result})

    def handle_post_reseller(self, body):
        try:
            un = body.get("username", "").strip()
            pwd = body.get("password", "") or generate_password()
            days = int(body.get("days", 30))
            max_users = int(body.get("max_users", 10))

            if not re.match(r'^[a-zA-Z0-9_]{3,32}$', un):
                return self.send_json(400, {"error": "Invalid username (3-32 chars, alphanumeric + underscore)"})

            # Check conflicts with admin username
            creds = get_panel_creds()
            if un == creds.get("PANEL_USER"):
                return self.send_json(400, {"error": "Username conflicts with admin"})

            resellers = read_resellers()
            if any(r["username"] == un for r in resellers):
                return self.send_json(400, {"error": "Reseller already exists"})

            new_r = {
                "username": un,
                "password": pwd,
                "expire_date": calculate_expire_date(days),
                "max_users": max_users,
                "enabled": True
            }
            resellers.append(new_r)
            write_resellers(resellers)
            self.send_json(200, new_r)
        except Exception as e:
            self.send_json(400, {"error": str(e)})

    def handle_put_reseller(self, username, body):
        resellers = read_resellers()
        idx = next((i for i, r in enumerate(resellers) if r["username"] == username), -1)
        if idx == -1:
            return self.send_json(404, {"error": "Reseller not found"})

        r = resellers[idx]
        if "password" in body and body["password"]:
            r["password"] = body["password"]
        if "days" in body:
            r["expire_date"] = calculate_expire_date(int(body["days"]))
        if "max_users" in body:
            r["max_users"] = int(body["max_users"])

        resellers[idx] = r
        write_resellers(resellers)
        self.send_json(200, r)

    def handle_toggle_reseller(self, username):
        resellers = read_resellers()
        idx = next((i for i, r in enumerate(resellers) if r["username"] == username), -1)
        if idx == -1:
            return self.send_json(404, {"error": "Reseller not found"})

        resellers[idx]["enabled"] = not resellers[idx]["enabled"]
        write_resellers(resellers)
        self.send_json(200, {"success": True, "enabled": resellers[idx]["enabled"]})

    def handle_delete_reseller(self, username, delete_users=False):
        resellers = read_resellers()
        idx = next((i for i, r in enumerate(resellers) if r["username"] == username), -1)
        if idx == -1:
            return self.send_json(404, {"error": "Reseller not found"})

        if delete_users:
            users = read_db()
            owned = [u for u in users if u.get("owner") == username]
            for u in owned:
                un = u["username"]
                run_cmd(["killall", "-u", un, "-9"], ignore_errors=True)
                run_cmd(["userdel", "-r", un], ignore_errors=True)
                run_cmd(f"rm -f {BW_DIR}/{un}.*", ignore_errors=True)
                run_cmd(f"rm -f /etc/firewallfalcon/banners/{un}.txt", ignore_errors=True)
            
            with db_lock:
                if os.path.exists(DB_FILE):
                    with open(DB_FILE, "r") as f:
                        lines = f.readlines()
                    owned_names = set(u["username"] for u in owned)
                    with open(DB_FILE, "w") as f:
                        for line in lines:
                            parts = line.strip().split(":")
                            if parts and parts[0] not in owned_names:
                                f.write(line)

        del resellers[idx]
        write_resellers(resellers)

        # Invalidate reseller's sessions
        tokens_to_remove = [t for t, s in sessions.items() if s.get("username") == username and s.get("role") == "reseller"]
        for t in tokens_to_remove:
            del sessions[t]

        self.send_json(200, {"success": True})

def main():
    os.makedirs(os.path.dirname(DB_FILE), exist_ok=True)
    server_address = ('0.0.0.0', PORT)
    httpd = ThreadingHTTPServer(server_address, PanelAPIHandler)
    print(f"Starting server on port {PORT}...", flush=True)
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    httpd.server_close()
    print("Server stopped.")

if __name__ == '__main__':
    main()
