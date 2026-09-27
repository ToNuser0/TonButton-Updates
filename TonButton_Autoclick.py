import os, sys, threading, time, ctypes, socket, struct, json, urllib.request, subprocess, math, glob
import customtkinter as ctk
from tkinter import filedialog, messagebox
import pydirectinput

# pydirectinputの内部遅延を無効化し最高精度にする
pydirectinput.PAUSE = 0
ctk.set_appearance_mode("Dark")
ctk.set_default_color_theme("blue")

CURRENT_VERSION = "1.0.7"
UPDATE_INFO_URL = "https://raw.githubusercontent.com/ToNuser0/TonButton-Updates/main/version.json"

DEFAULT_TIME_PARAMS = {
    "wait": 12.0, "fwd": 2.0, "left": 0.12, "standby_time": 420.0,
    "test_left": 0.6, "test_right": 0.6, "punish_thresh": 5.00, 
    "8page_thresh": 6.55, "back_time": 0.5, "max_recovery": 30.0
}

def resource_path(relative_path):
    try: return os.path.join(sys._MEIPASS, relative_path)
    except Exception: return os.path.join(os.path.abspath("."), relative_path)

def play_alert_sound(file_path):
    if not file_path or not os.path.exists(file_path): return
    try:
        wmm = ctypes.windll.winmm
        wmm.mciSendStringW('stop alert_sound', None, 0, None)
        wmm.mciSendStringW('close alert_sound', None, 0, None)
        wmm.mciSendStringW(f'open "{file_path}" alias alert_sound', None, 0, None)
        wmm.mciSendStringW('play alert_sound', None, 0, None)
    except Exception: pass

def parse_osc_floats(data):
    results = []
    try:
        if data.startswith(b'#bundle\x00'):
            offset = 16
            while offset < len(data):
                if offset + 4 > len(data): break
                size = struct.unpack(">I", data[offset:offset+4])[0]
                offset += 4
                if offset + size > len(data): break
                results.extend(parse_osc_floats(data[offset:offset+size]))
                offset += size
            return results
        idx = data.find(b'\x00')
        if idx == -1: return results
        addr = data[:idx].decode('utf-8', 'ignore')
        align_addr = (idx + 4) & ~3
        idx_type = data.find(b'\x00', align_addr)
        if idx_type == -1: return results
        if data[align_addr:idx_type].decode('utf-8', 'ignore').startswith(",f"):
            align_type = (idx_type + 4) & ~3
            if len(data) >= align_type + 4:
                results.append((addr, struct.unpack(">f", data[align_type:align_type+4])[0]))
    except Exception: pass
    return results

class VRCMacroApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title(f"TonButton_Autoclick.exe (v{CURRENT_VERSION})")
        self.geometry("600x480")
        self.minsize(500, 380)
        self.icon_path = resource_path("icon.ico")
        if os.path.exists(self.icon_path):
            try: self.iconbitmap(self.icon_path)
            except Exception: pass
            
        self.is_running = self.is_standby = self.has_recovered = self.is_testing_speed = False
        self.stop_event, self.app_exit_event, self.action_lock = threading.Event(), threading.Event(), threading.Lock()
        
        self.last_valid_time = self.last_action_end_time = time.time()
        self.last_event = "valid"
        self.punish_multiplier = 1.0
        self.osc_vel_x = self.osc_vel_y = self.osc_vel_z = self.osc_vel_mag = self.max_velocity_during_test = 0.0
        self.osc_last_mag_time = 0.0
        self.TARGET_KEYWORD = "Round was valid."
        self.settings_window = None

        self.time_params = DEFAULT_TIME_PARAMS.copy()
        self.log_path_var, self.mp3_punish_var, self.mp3_8page_var = ctk.StringVar(), ctk.StringVar(), ctk.StringVar()
        self.toggles = {
            "standby_resume": ctk.BooleanVar(value=False),
            "speed": ctk.BooleanVar(value=True),
            "recovery": ctk.BooleanVar(value=False)
        }
        self.time_vars = {k: ctk.StringVar(value=str(v)) for k, v in self.time_params.items()}

        self._load_config()
        self._bind_immediate_save()
        self._build_main_ui()
        self._auto_detect_log()
        
        threading.Thread(target=self._cleanup_old_versions, daemon=True).start()
        threading.Thread(target=self._update_worker, daemon=True).start()
        threading.Thread(target=self._integrated_monitor_worker, daemon=True).start()
        threading.Thread(target=self._osc_worker, daemon=True).start()

    def _bind_immediate_save(self):
        cb = lambda *args: self._save_config()
        self.log_path_var.trace_add("write", cb)
        self.mp3_punish_var.trace_add("write", cb)
        self.mp3_8page_var.trace_add("write", cb)
        for var in self.toggles.values(): var.trace_add("write", cb)
        
        for k, var in self.time_vars.items():
            def make_cb(key=k, v=var):
                def _cb(*args):
                    try: self.time_params[key] = float(v.get().strip()); self._save_config()
                    except ValueError: pass
                return _cb
            var.trace_add("write", make_cb())

    def _build_main_ui(self):
        container = ctk.CTkFrame(self)
        container.pack(fill="both", expand=True, padx=12, pady=12)

        f_log = ctk.CTkFrame(container)
        f_log.pack(fill="x", pady=(0, 10))
        ctk.CTkLabel(f_log, text="VRChat 監視ログ指定", font=ctk.CTkFont(size=13, weight="bold")).pack(anchor="w", padx=8, pady=(6, 0))
        row_log = ctk.CTkFrame(f_log, fg_color="transparent")
        row_log.pack(fill="x", padx=8, pady=(4, 8))
        ctk.CTkEntry(row_log, textvariable=self.log_path_var, placeholder_text="output_log のパス", height=28).pack(side="left", fill="x", expand=True, padx=(0, 8))
        ctk.CTkButton(row_log, text="参照...", width=60, height=28, command=self._browse_log_file).pack(side="left", padx=(0, 4))
        ctk.CTkButton(row_log, text="自動検出", width=70, height=28, fg_color="#3B8ED0", command=self._auto_detect_log).pack(side="left")

        f_ctrl = ctk.CTkFrame(container, fg_color="transparent")
        f_ctrl.pack(fill="x", pady=(0, 10))
        ctk.CTkButton(f_ctrl, text="⚙️ 各種設定...", width=120, height=38, fg_color="#484F58", hover_color="#30363D", font=ctk.CTkFont(weight="bold"), command=self._open_settings_dialog).pack(side="left", padx=(0, 12))
        self.btn_start = ctk.CTkButton(f_ctrl, text="▶ 実行開始", height=38, font=ctk.CTkFont(size=14, weight="bold"), fg_color="#2EA043", hover_color="#238636", command=self.start_macro)
        self.btn_start.pack(side="left", fill="x", expand=True, padx=(0, 6))
        self.btn_stop = ctk.CTkButton(f_ctrl, text="⏹ 停止", height=38, font=ctk.CTkFont(size=14, weight="bold"), fg_color="#DA3633", hover_color="#B62324", state="disabled", command=self.stop_macro)
        self.btn_stop.pack(side="left", fill="x", expand=True)

        ctk.CTkButton(container, text="📖 使用方法 (必ずお読みください)", height=32, fg_color="#1F6AA5", hover_color="#144870", command=self._show_help).pack(fill="x", pady=(0, 10))

        f_console = ctk.CTkFrame(container)
        f_console.pack(fill="both", expand=True)
        head = ctk.CTkFrame(f_console, fg_color="transparent")
        head.pack(fill="x", padx=8, pady=(4, 0))
        ctk.CTkLabel(head, text="動作ログ", font=ctk.CTkFont(size=12, weight="bold")).pack(side="left")
        ctk.CTkButton(head, text="クリア", width=50, height=20, fg_color="transparent", border_width=1, command=lambda: self.txt_console.configure(state="normal") or self.txt_console.delete("1.0", "end") or self.txt_console.configure(state="disabled")).pack(side="right")
        self.txt_console = ctk.CTkTextbox(f_console, wrap="word", font=ctk.CTkFont(family="Consolas", size=12))
        self.txt_console.pack(fill="both", expand=True, padx=8, pady=(4, 8))
        self.txt_console.configure(state="disabled")

    def _show_help(self):
        win = ctk.CTkToplevel(self)
        win.title("使用方法 - TonButton_Autoclick")
        win.geometry("560x560")
        win.attributes("-topmost", True)
        if os.path.exists(self.icon_path):
            try: win.iconbitmap(self.icon_path)
            except Exception: pass
        txt = ctk.CTkTextbox(win, wrap="word", font=ctk.CTkFont(size=13))
        txt.pack(fill="both", expand=True, padx=12, pady=12)
        txt.insert("1.0", """【TonButton_Autoclick の使用方法】

1. マクロの起動
画面上部の▶ 実行開始ボタンをクリックしてください。その後、VRChat内でリスポーン以外の方法でラウンドを1回終了させると、本マクロが稼働し始めます。

2. マクロの停止
長時間の休止やマクロを終了する際は、⏹ 停止ボタンをクリックするとすべての機能が停止します。

3. 動作環境についての注意
本マクロは、VRChatのウィンドウが最前面かつアクティブ（操作中）であることを想定しています。裏画面や別の操作をしている状態では正常に稼働しません。

4. 視点の調整について
マクロ動作中はアバターの視点の高さに応じた調整が必要です。
ビューポイント（視点）が中～高位置のアバターを使用している場合、起動トリガーとなるラウンド終了後、ロビーに着いたタイミングで視点を正面から少し下向きに調整してください。アバターに合わせて適宜微調整をお願いします。

5. 放置動作について
機能の放置稼働補助をオンにすることで、パニッシュ検知時や離席中の続行ラウンドに自動で対応し、完全放置での稼働が可能になります。
8Pageやパニッシュに対応して手動でアイテム回収を行いたい場合は、放置稼働補助をオフにしてください。オフにすると、速度異常検知時やメイン動作から30秒経過後にマクロが一時的に待機モード（スタンバイ）になり、操作を譲ります。その後、Round was valid.を検知した次のラウンドから再び通常稼働に戻ります。""")
        txt.configure(state="disabled")

    def _open_settings_dialog(self):
        if self.settings_window and self.settings_window.winfo_exists(): return self.settings_window.focus()
        self.settings_window = ctk.CTkToplevel(self)
        self.settings_window.title("各種設定")
        self.settings_window.geometry("560x600")
        self.settings_window.attributes("-topmost", True)
        if os.path.exists(self.icon_path):
            try: self.settings_window.iconbitmap(self.icon_path)
            except Exception: pass
            
        scroll = ctk.CTkScrollableFrame(self.settings_window)
        scroll.pack(fill="both", expand=True, padx=8, pady=8)

        def add_section(title):
            ctk.CTkLabel(scroll, text=title, font=ctk.CTkFont(size=13, weight="bold")).pack(anchor="w", pady=(4, 4))
            f = ctk.CTkFrame(scroll)
            f.pack(fill="x", pady=(0, 12), ipadx=8, ipady=8)
            return f

        f_toggles = add_section("【動作トグル設定】")
        ctk.CTkSwitch(f_toggles, text="【放置稼働補助】\n完全放置で稼働するようにする。offであれば半放置で稼働するようになる", variable=self.toggles["standby_resume"]).pack(anchor="w", padx=8, pady=6)
        ctk.CTkSwitch(f_toggles, text="【速度検知】\nボタン押下後、左右に移動してパニッシュや8Pageを検知する", variable=self.toggles["speed"]).pack(anchor="w", padx=8, pady=6)
        ctk.CTkSwitch(f_toggles, text="【リカバリー】\n長期間ラウンド終了がない場合、左右に移動しボタン押下で復帰を試みる", variable=self.toggles["recovery"]).pack(anchor="w", padx=8, pady=6)

        f_times = add_section("【各種時間・閾値設定】")
        def add_row(key, label):
            r = ctk.CTkFrame(f_times, fg_color="transparent")
            r.pack(fill="x", pady=2)
            ctk.CTkLabel(r, text=label, width=220, anchor="w").pack(side="left", padx=8)
            ctk.CTkEntry(r, height=26, width=100, textvariable=self.time_vars[key]).pack(side="right", padx=8)

        for k, l in [("wait", "待機時間 (秒):"), ("fwd", "前方移動時間 (秒):"), ("left", "左方移動時間 (秒):"), ("standby_time", "リカバリー移行待機時間 (秒):"), ("test_left", "速度検知 左移動 (秒):"), ("test_right", "速度検知 右移動 (秒):"), ("punish_thresh", "パニッシュ閾値速度:"), ("8page_thresh", "8Page閾値速度:"), ("back_time", "リカバリー 後退時間 (秒):"), ("max_recovery", "リカバリー 継続動作時間 (秒):")]: add_row(k, l)

        f_audio = add_section("【アラート音声設定】")
        for txt, var in [("パニッシュ:", self.mp3_punish_var), ("8Page:", self.mp3_8page_var)]:
            r = ctk.CTkFrame(f_audio, fg_color="transparent")
            r.pack(fill="x", pady=4)
            ctk.CTkLabel(r, text=txt, width=80, anchor="e").pack(side="left", padx=8)
            ctk.CTkEntry(r, textvariable=var).pack(side="left", fill="x", expand=True)
            ctk.CTkButton(r, text="参照...", width=60, command=lambda v=var: v.set(filedialog.askopenfilename(filetypes=[("Audio", "*.mp3;*.wav"), ("All", "*.*")]) or v.get())).pack(side="left", padx=8)

        ctk.CTkButton(scroll, text="閉じる", height=38, font=ctk.CTkFont(weight="bold"), fg_color="#484F58", hover_color="#30363D", command=self.settings_window.destroy).pack(fill="x", padx=12, pady=12)

    def _get_config_path(self): return os.path.join(os.path.dirname(sys.executable) if getattr(sys, 'frozen', False) else "", "TonButton_Config.json")

    def _save_config(self):
        try:
            with open(self._get_config_path(), "w", encoding="utf-8") as f:
                json.dump({"log_path": self.log_path_var.get().strip(), "mp3_punish": self.mp3_punish_var.get().strip(), "mp3_8page": self.mp3_8page_var.get().strip(), "time_params": self.time_params, "toggles": {k: v.get() for k, v in self.toggles.items()}}, f, ensure_ascii=False, indent=4)
        except Exception: pass

    def _load_config(self):
        if not os.path.exists(self._get_config_path()): return
        try:
            with open(self._get_config_path(), "r", encoding="utf-8") as f: c = json.load(f)
            self.log_path_var.set(c.get("log_path", ""))
            self.mp3_punish_var.set(c.get("mp3_punish", ""))
            self.mp3_8page_var.set(c.get("mp3_8page", ""))
            if "time_params" in c: self.time_params.update(c["time_params"])
            if "toggles" in c: [self.toggles[k].set(v) for k, v in c["toggles"].items() if k in self.toggles]
        except Exception: pass

    def log(self, msg):
        def _append():
            self.txt_console.configure(state="normal")
            self.txt_console.insert("end", f"[{datetime.datetime.now().strftime('%H:%M:%S')}] {msg}\n")
            if int(self.txt_console.index("end-1c").split(".")[0]) > 500: self.txt_console.delete("1.0", "end-500l")
            self.txt_console.see("end")
            self.txt_console.configure(state="disabled")
        self.after(0, _append)

    def _browse_log_file(self):
        if sel := filedialog.askopenfilename(title="output_log を選択", filetypes=[("Text", "output_log_*.txt;*.txt"), ("All", "*.*")]): self.log_path_var.set(sel)

    def _auto_detect_log(self):
        files = glob.glob(os.path.expandvars(r"%USERPROFILE%\AppData\LocalLow\VRChat\VRChat\output_log_*.txt"))
        if files:
            latest = max(files, key=os.path.getmtime)
            self.log_path_var.set(latest)
            self.log(f"最新ログ検出: {os.path.basename(latest)}")

    def _safe_sleep(self, sec): return not self.stop_event.wait(sec)
    def _release_all_inputs(self): [pydirectinput.keyUp(k) for k in ('w', 'a', 's', 'd')]; pydirectinput.mouseUp()

    def start_macro(self):
        if not os.path.exists(self.log_path_var.get().strip()): return messagebox.showerror("エラー", "正しいログファイルを指定してください。")
        self._save_config()
        self.is_running, self.is_standby, self.has_recovered = True, False, False
        self.stop_event.clear()
        self.last_valid_time = self.last_action_end_time = time.time()
        self.last_event = "valid"
        self.btn_start.configure(state="disabled")
        self.btn_stop.configure(state="normal")
        self.log("=== 実行を開始しました ===")

    def stop_macro(self):
        if not self.is_running: return
        self.is_running = False
        self.stop_event.set()
        self._release_all_inputs()
        self.btn_start.configure(state="normal")
        self.btn_stop.configure(state="disabled")
        self.log("=== 停止しました ===")

    def _integrated_monitor_worker(self):
        cur_log, f, last_scan = "", None, 0
        while not self.app_exit_event.is_set():
            time.sleep(0.5)
            target = self.log_path_var.get().strip()
            
            if time.time() - last_scan > 5.0:
                last_scan = time.time()
                files = glob.glob(os.path.expandvars(r"%USERPROFILE%\AppData\LocalLow\VRChat\VRChat\output_log_*.txt"))
                if files and (latest := max(files, key=os.path.getmtime)) != target and (not target or os.path.getmtime(latest) > os.path.getmtime(target)):
                    self.log_path_var.set(latest)
                    target = latest
                    self.log(f"【自動追従】新しいログファイルを検出しました: {os.path.basename(latest)}")

            if not target or not os.path.exists(target): continue
            
            if not f or cur_log != target:
                if f: f.close()
                try:
                    f = open(target, "r", encoding="utf-8", errors="ignore")
                    f.seek(0, os.SEEK_END)
                    cur_log = target
                except Exception: f = None; continue

            found_round = any(self.TARGET_KEYWORD in line for line in f)
            if not self.is_running: continue

            e_val, e_act = time.time() - self.last_valid_time, time.time() - self.last_action_end_time

            # 30秒でのラウンド間スタンバイ (無条件: アクション後30秒で移行)
            if not self.is_standby and self.last_event == "action" and e_act >= 30.0:
                self.is_standby = True
                self.log("【STANDBY】ラウンド間の待機モードに移行しました。")

            # リカバリー発動 (長期間未検知)
            if not self.has_recovered and e_val >= self.time_params["standby_time"]:
                self.has_recovered = True
                if self.toggles["recovery"].get():
                    self.log("【リカバリー】長期間応答がないため、復帰動作を開始します。")
                    threading.Thread(target=self._execute_recovery_action, daemon=True).start()

            # メイン動作
            if found_round:
                self.has_recovered = False
                should_execute = True
                if self.is_standby:
                    self.is_standby = False
                    if self.toggles["standby_resume"].get():
                        self.log("【ACTIVE】ラウンド終了検知。放置補助ONのため待機モードを解除し稼働します。")
                    else:
                        self.log("【ACTIVE】ラウンド終了検知。待機モードを解除しました。(次回ラウンドから通常稼働)")
                        should_execute = False
                
                self.last_valid_time = time.time()
                self.last_event = "valid"
                if should_execute: threading.Thread(target=self._execute_main_action, daemon=True).start()

    def _execute_recovery_action(self):
        if not self.action_lock.acquire(blocking=False): return
        try:
            self.log("リカバリー動作(後退)を実行します...")
            pydirectinput.keyDown('s')
            if not self._safe_sleep(self.time_params["back_time"]): return
            pydirectinput.keyUp('s')
            if not self._safe_sleep(0.1): return
            
            self.log("リカバリー動作(左右Use連打)を開始します。")
            rec_start, is_right = time.time(), True
            while time.time() - rec_start < self.time_params["max_recovery"] and self.is_running and self.is_standby:
                key = 'd' if is_right else 'a'
                pydirectinput.keyDown(key)
                step_end = time.time() + 3.0
                while time.time() < step_end and self.is_running and self.is_standby:
                    pydirectinput.mouseDown()
                    if not self._safe_sleep(0.05): return
                    pydirectinput.mouseUp()
                    if not self._safe_sleep(0.1): return
                pydirectinput.keyUp(key)
                is_right = not is_right
            self.log("リカバリー動作が終了、または中断されました。")
        finally:
            self._release_all_inputs()
            self.action_lock.release()

    def _execute_main_action(self):
        if not self.action_lock.acquire(blocking=False): return
        try:
            self.log(f"検知: '{self.TARGET_KEYWORD}' -> 自動ボタン押下開始")
            if not self._safe_sleep(self.time_params["wait"]): return
            
            mul = self.punish_multiplier
            self.punish_multiplier = 1.0
            if mul > 1.0: self.log(f"【パニッシュ対応】移動時間を {mul}倍 にして実行します。")
            
            def move(key, dur):
                pydirectinput.keyDown(key)
                res = self._safe_sleep(dur)
                pydirectinput.keyUp(key)
                return res

            self.log("前方(W)へ移動")
            if not move('w', self.time_params["fwd"] * mul) or not self._safe_sleep(0.1): return
            self.log("左方(A)へ移動")
            if not move('a', self.time_params["left"] * mul) or not self._safe_sleep(0.2): return
            
            self.log("オブジェクトをUse (クリック)")
            pydirectinput.mouseDown()
            if not self._safe_sleep(0.1): return
            pydirectinput.mouseUp()
            self.log("自動ボタン押下完了。")

            if self.toggles["speed"].get():
                self.log("【速度検知】左右移動を開始します...")
                self.osc_vel_x = self.osc_vel_y = self.osc_vel_z = self.osc_vel_mag = self.max_velocity_during_test = 0.0
                self.is_testing_speed = True
                
                if not move('d', self.time_params["test_right"]) or not self._safe_sleep(0.1): return
                if not move('a', self.time_params["test_left"]) or not self._safe_sleep(0.1): return
                self.is_testing_speed = False
                
                v = self.max_velocity_during_test
                if v == 0.0: self.log("【警告】最大速度が0.0でした。OSCが受信できていない可能性があります。")
                else: self.log(f"検知終了。最大速度: {v:.3f}")
                
                t1, t2 = self.time_params["punish_thresh"], self.time_params["8page_thresh"]
                matched = "punish" if v < t1 and v < t2 else "8page" if v < t2 else None
                
                if matched:
                    play_alert_sound(self.mp3_punish_var.get().strip() if matched == "punish" else self.mp3_8page_var.get().strip())
                    if not self.toggles["standby_resume"].get():
                        self.log(f"【警告】速度が{matched}閾値未満。放置補助OFFのため待機モードに移行します。")
                        self.punish_multiplier = 1.0
                        self.is_standby = True
                    else:
                        if matched == "punish":
                            self.log(f"【警告】速度がパニッシュ閾値未満。次回メイン動作の移動時間を1.66倍します。")
                            self.punish_multiplier = 1.66
                        else: self.log(f"【警告】速度が8Page閾値未満です。")
                else: self.log("速度は正常です。")
        finally:
            self.last_action_end_time = time.time()
            self.last_event = "action"
            self._release_all_inputs()
            self.action_lock.release()

    def _osc_worker(self):
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 65536)
        try: 
            sock.bind(("0.0.0.0", 9001))
            self.after(1000, lambda: self.log("【OSC】ポート9001での受信待機を開始しました。"))
        except Exception as e: return self.after(1000, lambda: self.log(f"【OSCエラー】ポートのバインドに失敗しました。({e})"))
            
        sock.settimeout(0.1)
        first_receive = True
        while not self.app_exit_event.is_set():
            try:
                data, _ = sock.recvfrom(65536)
                if first_receive:
                    self.after(0, lambda: self.log("【OSC】VRChatからのOSC初回到達を確認しました。"))
                    first_receive = False
                for addr, val in parse_osc_floats(data):
                    if addr == "/avatar/parameters/VelocityMagnitude": self.osc_vel_mag = val; self.osc_last_mag_time = time.time()
                    elif addr == "/avatar/parameters/VelocityX": self.osc_vel_x = val
                    elif addr == "/avatar/parameters/VelocityY": self.osc_vel_y = val
                    elif addr == "/avatar/parameters/VelocityZ": self.osc_vel_z = val
                
                self.current_velocity = self.osc_vel_mag if time.time() - self.osc_last_mag_time < 2.0 else math.sqrt(self.osc_vel_x**2 + self.osc_vel_y**2 + self.osc_vel_z**2)
                if self.is_testing_speed: self.max_velocity_during_test = max(self.max_velocity_during_test, self.current_velocity)
            except Exception: pass
        sock.close()

    def _cleanup_old_versions(self):
        if not getattr(sys, 'frozen', False): return
        current_exe = os.path.abspath(sys.executable)
        for _ in range(5):
            time.sleep(2.0)
            if all((os.remove(f) or self.log(f"【クリーン】旧バージョン削除: {os.path.basename(f)}")) if os.path.abspath(f) != current_exe else True for f in glob.glob(os.path.join(os.path.dirname(current_exe), "TonButton_Autoclick*.exe"))): break

    def _update_worker(self):
        if not getattr(sys, 'frozen', False): return
        try:
            with urllib.request.urlopen(urllib.request.Request(UPDATE_INFO_URL, headers={'User-Agent': 'Mozilla/5.0'}), timeout=5) as res:
                data = json.loads(res.read().decode('utf-8'))
            if data.get("version") and data.get("version") != CURRENT_VERSION:
                self.after(0, lambda: self._prompt_update(data.get("version"), data.get("url"), data.get("release_notes", "")))
        except Exception: pass 

    def _prompt_update(self, version, url, notes):
        if messagebox.askyesno("アップデート通知", f"新しいバージョン (v{version}) が見つかりました。\n\n【アップデート内容】\n{notes}\n\n今すぐ自動アップデートしますか？"):
            self.btn_start.configure(state="disabled")
            self.btn_stop.configure(state="disabled")
            self.log(f"v{version} のダウンロードを開始しました...")
            threading.Thread(target=self._download_and_apply_update, args=(url, version), daemon=True).start()

    def _download_and_apply_update(self, download_url, version):
        try:
            new_exe = os.path.join(os.path.dirname(sys.executable), f"TonButton_Autoclick_v{version}.exe")
            with urllib.request.urlopen(urllib.request.Request(download_url, headers={'User-Agent': 'Mozilla/5.0'}), timeout=60) as res:
                total, downloaded = int(res.headers.get('Content-Length', 0)), 0
                with open(new_exe, 'wb') as f:
                    while chunk := res.read(8192): f.write(chunk); downloaded += len(chunk)
            if total > 0 and downloaded != total: raise Exception("通信切断")
            self.log("ダウンロード完了。再起動します...")
            os.startfile(new_exe)
            self.after(500, lambda: self._save_config() or self.stop_event.set() or self.app_exit_event.set() or self.after(500, lambda: self.destroy() or sys.exit(0)))
        except Exception as e:
            self.after(0, lambda: self.log(f"【エラー】アップデート失敗: {e}") or self.btn_start.configure(state="normal"))

    def _on_closing(self):
        self._save_config()
        self.stop_event.set()
        self.app_exit_event.set()
        self.after(500, lambda: self.destroy() or sys.exit(0))

if __name__ == "__main__":
    app = VRCMacroApp()
    app.mainloop()