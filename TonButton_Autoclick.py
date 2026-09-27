import datetime
import glob
import os
import sys
import threading
import time
import ctypes
import socket
import struct
import json
import urllib.request
import subprocess
import math
import customtkinter as ctk
from tkinter import filedialog, messagebox
import pydirectinput

# pydirectinputの内部遅延を無効化し最高精度にする
pydirectinput.PAUSE = 0

# 外観設定
ctk.set_appearance_mode("Dark")
ctk.set_default_color_theme("blue")

# ==========================================
# 🔧 【開発者設定】自動アップデート用の設定
# ==========================================
CURRENT_VERSION = "1.0.6"
UPDATE_INFO_URL = "https://raw.githubusercontent.com/ToNuser0/TonButton-Updates/main/version.json"
# ==========================================

# 時間パラメーターの初期デフォルト設定
DEFAULT_TIME_PARAMS = {
    "wait": 11.0,
    "fwd": 2.0,
    "left": 0.1,
    "test_left": 0.5,
    "test_right": 0.5,
    "punish_thresh": 5.00,
    "8page_thresh": 6.55,
    "standby_time": 420.0,  # 7分
    "back_time": 0.5,
    "max_recovery": 30.0
}

def resource_path(relative_path):
    try: base_path = sys._MEIPASS
    except Exception: base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)

# --- MP3再生 (WinMM使用・非同期・超軽量) ---
def play_alert_sound(file_path):
    if not os.path.exists(file_path) or not file_path: return
    try:
        ctypes.windll.winmm.mciSendStringW('stop alert_sound', None, 0, None)
        ctypes.windll.winmm.mciSendStringW('close alert_sound', None, 0, None)
        cmd_open = f'open "{file_path}" alias alert_sound'
        ctypes.windll.winmm.mciSendStringW(cmd_open, None, 0, None)
        ctypes.windll.winmm.mciSendStringW('play alert_sound', None, 0, None)
    except Exception: pass

# --- OSCパケット解析 ---
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

        null_idx = data.find(b'\x00')
        if null_idx == -1: return results
        addr = data[:null_idx].decode('utf-8', 'ignore')
        
        align_addr = (null_idx + 4) & ~3
        null_idx_type = data.find(b'\x00', align_addr)
        if null_idx_type == -1: return results
        type_tags = data[align_addr:null_idx_type].decode('utf-8', 'ignore')
        
        if type_tags.startswith(",f"):
            align_type = (null_idx_type + 4) & ~3
            if len(data) >= align_type + 4:
                val = struct.unpack(">f", data[align_type:align_type+4])[0]
                results.append((addr, val))
    except Exception: pass
    return results


class VRCMacroApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title(f"TonButton_Autoclick.exe (v{CURRENT_VERSION})")
        self.geometry("600x480")
        self.minsize(500, 380)
        self.resizable(True, True)
        self.protocol("WM_DELETE_WINDOW", self._on_closing)
        
        # アイコン適用
        self.icon_path = resource_path("icon.ico")
        if os.path.exists(self.icon_path):
            try: self.iconbitmap(self.icon_path)
            except Exception: pass
        
        # --- 変数定義 ---
        self.is_running = False
        self.stop_event = threading.Event()
        self.app_exit_event = threading.Event()
        self.action_lock = threading.Lock() 
        self.is_standby = False
        self.last_valid_time = time.time()
        
        # パニッシュ時、次回動作を1.66倍にするためのフラグ
        self.punish_multiplier = 1.0
        
        self.time_params = DEFAULT_TIME_PARAMS.copy()
        
        # UI連動用の設定変数
        self.log_path_var = ctk.StringVar()
        self.mp3_punish_var = ctk.StringVar()
        self.mp3_8page_var = ctk.StringVar()
        
        self.toggles = {
            "standby_resume": ctk.BooleanVar(value=True),
            "speed": ctk.BooleanVar(value=True),
            "recovery": ctk.BooleanVar(value=False)
        }
        
        # 速度テスト用共有変数
        self.current_velocity = 0.0
        self.max_velocity_during_test = 0.0
        self.is_testing_speed = False
        self.osc_vel_x = 0.0
        self.osc_vel_y = 0.0
        self.osc_vel_z = 0.0
        self.osc_vel_mag = 0.0
        self.osc_last_mag_time = 0.0
        
        self.TARGET_KEYWORD = "Round was valid."
        
        self.settings_window = None
        
        # --- 処理開始 ---
        self._load_config()
        self._build_main_ui()
        self._auto_detect_log()
        self._cleanup_old_versions()

        self.integrated_monitor_thread = threading.Thread(target=self._integrated_monitor_worker, daemon=True)
        self.integrated_monitor_thread.start()
        
        self.osc_thread = threading.Thread(target=self._osc_worker, daemon=True)
        self.osc_thread.start()

        self._check_for_updates()

    # ==========================================
    # 🖥 UI構築 (メイン画面)
    # ==========================================
    def _build_main_ui(self):
        container = ctk.CTkFrame(self)
        container.pack(fill="both", expand=True, padx=12, pady=12)

        # ① 監視ログ
        f_log = ctk.CTkFrame(container)
        f_log.pack(fill="x", pady=(0, 10))
        ctk.CTkLabel(f_log, text="VRChat 監視ログ指定", font=ctk.CTkFont(size=13, weight="bold")).pack(anchor="w", padx=8, pady=(6, 0))
        
        row_log = ctk.CTkFrame(f_log, fg_color="transparent")
        row_log.pack(fill="x", padx=8, pady=(4, 8))
        entry_log = ctk.CTkEntry(row_log, textvariable=self.log_path_var, placeholder_text="output_log のパス", height=28)
        entry_log.pack(side="left", fill="x", expand=True, padx=(0, 8))
        ctk.CTkButton(row_log, text="参照...", width=60, height=28, command=self._browse_log_file).pack(side="left", padx=(0, 4))
        ctk.CTkButton(row_log, text="自動検出", width=70, height=28, fg_color="#3B8ED0", command=self._auto_detect_log).pack(side="left")

        # ② コントロール類
        f_ctrl = ctk.CTkFrame(container, fg_color="transparent")
        f_ctrl.pack(fill="x", pady=(0, 10))
        
        btn_settings = ctk.CTkButton(f_ctrl, text="⚙️ 各種設定...", width=120, height=38, fg_color="#484F58", hover_color="#30363D", font=ctk.CTkFont(weight="bold"), command=self._open_settings_dialog)
        btn_settings.pack(side="left", padx=(0, 12))
        
        self.btn_start = ctk.CTkButton(f_ctrl, text="▶ 実行開始", height=38, font=ctk.CTkFont(size=14, weight="bold"), fg_color="#2EA043", hover_color="#238636", command=self.start_macro)
        self.btn_start.pack(side="left", fill="x", expand=True, padx=(0, 6))
        
        self.btn_stop = ctk.CTkButton(f_ctrl, text="⏹ 停止", height=38, font=ctk.CTkFont(size=14, weight="bold"), fg_color="#DA3633", hover_color="#B62324", state="disabled", command=self.stop_macro)
        self.btn_stop.pack(side="left", fill="x", expand=True, padx=(0, 0))

        # 使用方法ボタン
        btn_help = ctk.CTkButton(container, text="📖 使用方法 (必ずお読みください)", height=32, fg_color="#1F6AA5", hover_color="#144870", command=self._show_help)
        btn_help.pack(fill="x", pady=(0, 10))

        # ③ 動作コンソール
        f_console = ctk.CTkFrame(container)
        f_console.pack(fill="both", expand=True)
        head_console = ctk.CTkFrame(f_console, fg_color="transparent")
        head_console.pack(fill="x", padx=8, pady=(4, 0))
        ctk.CTkLabel(head_console, text="動作ログ", font=ctk.CTkFont(size=12, weight="bold")).pack(side="left")
        ctk.CTkButton(head_console, text="クリア", width=50, height=20, fg_color="transparent", border_width=1, command=self._clear_log).pack(side="right")
        
        self.txt_console = ctk.CTkTextbox(f_console, wrap="word", font=ctk.CTkFont(family="Consolas", size=12))
        self.txt_console.pack(fill="both", expand=True, padx=8, pady=(4, 8))
        self.txt_console.configure(state="disabled")

    # ==========================================
    # 📖 使用方法ポップアップ窓
    # ==========================================
    def _show_help(self):
        help_win = ctk.CTkToplevel(self)
        help_win.title("使用方法 - TonButton_Autoclick")
        help_win.geometry("540x420")
        help_win.attributes("-topmost", True)
        
        if os.path.exists(self.icon_path):
            try: help_win.iconbitmap(self.icon_path)
            except Exception: pass
            
        textbox = ctk.CTkTextbox(help_win, wrap="word", font=ctk.CTkFont(size=13))
        textbox.pack(fill="both", expand=True, padx=12, pady=12)
        
        help_text = """【TonButton_Autoclick の使用方法】

1. マクロの起動
画面上の▶ 実行開始ボタンをクリックしてください。
その後、VRChat内でリスポーン以外の方法でラウンドを1回終了させると、自動的にマクロが稼働し始めます。

2. マクロの停止
長時間ゲームを離れる際や一時的にマクロを終了したい場合は、⏹ 停止ボタンをクリックするとすべての自動操作が停止します。

3. 動作環境についての注意
本マクロは、VRChatのウィンドウが最前面かつアクティブ（操作中）の状態であることを前提としています。別のウィンドウを操作している裏画面の状態では正常に稼働しません。

4. 視点の調整について
マクロ動作中は、アバターの視点の高さに応じた調整が必要です。
ビューポイント（視点）が中～高位置のアバターを使用している場合、マクロ起動のトリガーとなるラウンド終了後、ロビーに戻ったタイミングで視点を正面から下向きに調整してください。アバターに合わせて適宜微調整をお願いします。
"""
        textbox.insert("1.0", help_text)
        textbox.configure(state="disabled")

    # ==========================================
    # ⚙️ UI構築 (設定ポップアップ窓)
    # ==========================================
    def _open_settings_dialog(self):
        if self.settings_window is not None and self.settings_window.winfo_exists():
            self.settings_window.focus()
            return

        self.settings_window = ctk.CTkToplevel(self)
        self.settings_window.title("各種設定 - TonButton_Autoclick")
        self.settings_window.geometry("560x580")
        self.settings_window.resizable(True, True)
        self.settings_window.attributes("-topmost", True)
        
        if os.path.exists(self.icon_path):
            try: self.settings_window.iconbitmap(self.icon_path)
            except Exception: pass
            
        scroll = ctk.CTkScrollableFrame(self.settings_window)
        scroll.pack(fill="both", expand=True, padx=8, pady=8)

        # --- トグルスイッチ群 ---
        ctk.CTkLabel(scroll, text="【動作トグル設定】", font=ctk.CTkFont(size=13, weight="bold")).pack(anchor="w", pady=(4, 4))
        f_toggles = ctk.CTkFrame(scroll)
        f_toggles.pack(fill="x", pady=(0, 12), ipadx=8, ipady=8)
        
        ctk.CTkSwitch(f_toggles, text="【続行ラウンド待機および稼働復帰】\n続行ラウンドで稼働を一時スタンバイさせ、終了時に自動で解除する", variable=self.toggles["standby_resume"]).pack(anchor="w", padx=8, pady=6)
        ctk.CTkSwitch(f_toggles, text="【速度検知】\nボタン押下後、左右に移動してパニッシュや8Pageを検知する", variable=self.toggles["speed"]).pack(anchor="w", padx=8, pady=6)
        ctk.CTkSwitch(f_toggles, text="【リカバリー】\n長期間ラウンド終了がない場合、左右に移動しボタン押下で復帰を試みる", variable=self.toggles["recovery"]).pack(anchor="w", padx=8, pady=6)

        time_entries = {}
        
        # --- 時間パラメーター群 ---
        ctk.CTkLabel(scroll, text="【各種時間・閾値設定】", font=ctk.CTkFont(size=13, weight="bold")).pack(anchor="w", pady=(4, 4))
        f_times = ctk.CTkFrame(scroll)
        f_times.pack(fill="x", pady=(0, 12), ipadx=8, ipady=8)
        
        def add_time_row(parent, key, label):
            row = ctk.CTkFrame(parent, fg_color="transparent")
            row.pack(fill="x", pady=2)
            ctk.CTkLabel(row, text=label, width=220, anchor="w").pack(side="left", padx=8)
            e = ctk.CTkEntry(row, height=26, width=100)
            e.insert(0, str(self.time_params.get(key, "")))
            e.pack(side="right", padx=8)
            time_entries[key] = e

        add_time_row(f_times, "wait", "待機時間 (秒):")
        add_time_row(f_times, "fwd", "前方移動時間 (秒):")
        add_time_row(f_times, "left", "左方移動時間 (秒):")
        add_time_row(f_times, "standby_time", "スタンバイ移行時間 (秒):")
        add_time_row(f_times, "test_left", "速度検知 左移動 (秒):")
        add_time_row(f_times, "test_right", "速度検知 右移動 (秒):")
        add_time_row(f_times, "punish_thresh", "パニッシュ閾値速度:")
        add_time_row(f_times, "8page_thresh", "8Page閾値速度:")
        add_time_row(f_times, "back_time", "リカバリー 後退時間 (秒):")
        add_time_row(f_times, "max_recovery", "リカバリー 継続動作時間 (秒):")

        # --- 音声設定群 ---
        ctk.CTkLabel(scroll, text="【アラート音声設定】", font=ctk.CTkFont(size=13, weight="bold")).pack(anchor="w", pady=(4, 4))
        f_audio = ctk.CTkFrame(scroll)
        f_audio.pack(fill="x", pady=(0, 12), ipadx=8, ipady=8)

        def browse_audio(var):
            sel = filedialog.askopenfilename(title="アラート音声を選択", filetypes=[("Audio", "*.mp3;*.wav"), ("All", "*.*")])
            if sel: var.set(sel)

        row_p = ctk.CTkFrame(f_audio, fg_color="transparent")
        row_p.pack(fill="x", pady=4)
        ctk.CTkLabel(row_p, text="パニッシュ:", width=80, anchor="e").pack(side="left", padx=8)
        ctk.CTkEntry(row_p, textvariable=self.mp3_punish_var).pack(side="left", fill="x", expand=True)
        ctk.CTkButton(row_p, text="参照...", width=60, command=lambda: browse_audio(self.mp3_punish_var)).pack(side="left", padx=8)

        row_8 = ctk.CTkFrame(f_audio, fg_color="transparent")
        row_8.pack(fill="x", pady=4)
        ctk.CTkLabel(row_8, text="8Page:", width=80, anchor="e").pack(side="left", padx=8)
        ctk.CTkEntry(row_8, textvariable=self.mp3_8page_var).pack(side="left", fill="x", expand=True)
        ctk.CTkButton(row_8, text="参照...", width=60, command=lambda: browse_audio(self.mp3_8page_var)).pack(side="left", padx=8)

        # --- 保存ボタン ---
        def save_and_close():
            try:
                for k, e in time_entries.items():
                    self.time_params[k] = float(e.get().strip())
                self._save_config()
                self.log("【設定】各種設定を更新・保存しました。")
                self.settings_window.destroy()
            except ValueError:
                messagebox.showerror("入力エラー", "時間/閾値にはすべて数値を入力してください。", parent=self.settings_window)

        btn_save = ctk.CTkButton(scroll, text="設定を保存して閉じる", height=38, font=ctk.CTkFont(weight="bold"), fg_color="#2EA043", hover_color="#238636", command=save_and_close)
        btn_save.pack(fill="x", padx=12, pady=(12, 12))
        self.settings_window.protocol("WM_DELETE_WINDOW", save_and_close)


    # ==========================================
    # 🔧 設定の保存と読み込み
    # ==========================================
    def _get_config_path(self):
        if getattr(sys, 'frozen', False):
            return os.path.join(os.path.dirname(sys.executable), "TonButton_Config.json")
        return "TonButton_Config.json"

    def _save_config(self):
        try:
            config = {
                "log_path": self.log_path_var.get().strip(),
                "mp3_punish": self.mp3_punish_var.get().strip(),
                "mp3_8page": self.mp3_8page_var.get().strip(),
                "time_params": self.time_params,
                "toggles": { k: v.get() for k, v in self.toggles.items() }
            }
            with open(self._get_config_path(), "w", encoding="utf-8") as f:
                json.dump(config, f, ensure_ascii=False, indent=4)
        except Exception: pass

    def _load_config(self):
        try:
            path = self._get_config_path()
            if os.path.exists(path):
                with open(path, "r", encoding="utf-8") as f: config = json.load(f)
                
                self.log_path_var.set(config.get("log_path", ""))
                self.mp3_punish_var.set(config.get("mp3_punish", ""))
                self.mp3_8page_var.set(config.get("mp3_8page", ""))
                
                if "time_params" in config and isinstance(config["time_params"], dict):
                    # 古い設定からのマージ（不足キーの補完）
                    for k, v in DEFAULT_TIME_PARAMS.items():
                        if k not in config["time_params"]:
                            config["time_params"][k] = v
                    self.time_params.update(config["time_params"])
                    
                if "toggles" in config and isinstance(config["toggles"], dict):
                    for k, val in config["toggles"].items():
                        if k in self.toggles:
                            self.toggles[k].set(val)
                        # 古い設定ファイルからの引き継ぎ
                        elif k == "standby" and "standby_resume" in self.toggles:
                            self.toggles["standby_resume"].set(val)
        except Exception: pass

    # ==========================================
    # ⚙️ アプリ基盤ロジック群
    # ==========================================
    def log(self, message):
        timestamp = datetime.datetime.now().strftime("%H:%M:%S")
        formatted = f"[{timestamp}] {message}\n"
        def _append():
            self.txt_console.configure(state="normal")
            self.txt_console.insert("end", formatted)
            total = int(self.txt_console.index("end-1c").split(".")[0])
            if total > 500: self.txt_console.delete("1.0", f"{total - 500 + 1}.0")
            self.txt_console.see("end")
            self.txt_console.configure(state="disabled")
        self.after(0, _append)

    def _clear_log(self):
        self.txt_console.configure(state="normal")
        self.txt_console.delete("1.0", "end")
        self.txt_console.configure(state="disabled")

    def _browse_log_file(self):
        sel = filedialog.askopenfilename(title="output_log を選択", filetypes=[("Text", "output_log_*.txt;*.txt"), ("All", "*.*")])
        if sel:
            self.log_path_var.set(sel)
            self._save_config()

    def _auto_detect_log(self):
        log_dir = os.path.expandvars(r"%USERPROFILE%\AppData\LocalLow\VRChat\VRChat")
        files = glob.glob(os.path.join(log_dir, "output_log_*.txt"))
        if files:
            latest = max(files, key=os.path.getmtime)
            self.log_path_var.set(latest)
            self.log(f"最新ログ検出: {os.path.basename(latest)}")

    def _safe_sleep(self, seconds, check_stop=True):
        if not check_stop: return True
        return not self.stop_event.wait(seconds)

    def _release_all_inputs(self):
        for key in ('w', 'a', 's', 'd'): pydirectinput.keyUp(key)
        pydirectinput.mouseUp()

    def start_macro(self):
        if not os.path.exists(self.log_path_var.get().strip()):
            messagebox.showerror("エラー", "正しいログファイルを指定してください。")
            return

        self._save_config()
        self.is_running = True
        self.is_standby = False
        self.stop_event.clear()
        self.last_valid_time = time.time()
        
        self.btn_start.configure(state="disabled")
        self.btn_stop.configure(state="normal")
        self.log("=== 実行を開始しました ===")

    def stop_macro(self):
        if not self.is_running: return
        self.log("停止リクエストを受信。停止中...")
        self.is_running = False
        self.stop_event.set()
        self._release_all_inputs()
        self.btn_start.configure(state="normal")
        self.btn_stop.configure(state="disabled")
        self.log("=== 停止しました ===")

    # ==========================================
    # 🧠 メイン監視・実行ロジック
    # ==========================================
    def _integrated_monitor_worker(self):
        current_log_path = ""
        f = None
        last_dir_scan = 0
        
        while not self.app_exit_event.is_set():
            time.sleep(0.5)
            target_log = self.log_path_var.get().strip()
            
            if time.time() - last_dir_scan > 5.0:
                last_dir_scan = time.time()
                log_dir = os.path.expandvars(r"%USERPROFILE%\AppData\LocalLow\VRChat\VRChat")
                files = glob.glob(os.path.join(log_dir, "output_log_*.txt"))
                if files:
                    latest_log = max(files, key=os.path.getmtime)
                    if target_log and latest_log != target_log and os.path.getmtime(latest_log) > os.path.getmtime(target_log):
                        self.log_path_var.set(latest_log)
                        target_log = latest_log
                        self.log(f"【自動追従】新しいログファイルを検出しました: {os.path.basename(latest_log)}")

            if not target_log or not os.path.exists(target_log): continue
            
            if not f or current_log_path != target_log:
                if f: f.close()
                try:
                    f = open(target_log, "r", encoding="utf-8", errors="ignore")
                    f.seek(0, os.SEEK_END)
                    current_log_path = target_log
                except Exception:
                    f = None
                    continue

            found_round = False
            
            while True:
                line = f.readline()
                if not line: break
                if self.TARGET_KEYWORD in line: found_round = True

            if not self.is_running: continue

            # --- 長期間待機(スタンバイ/リカバリー)の判定 ---
            if not self.is_standby and time.time() - self.last_valid_time >= self.time_params["standby_time"]:
                self.is_standby = True
                
                if self.toggles["standby_resume"].get():
                    self.log("【STANDBY】続行ラウンド待機のため、稼働を一時的にスタンバイします。")
                    
                if self.toggles["recovery"].get():
                    self.log("【リカバリー】長期間ラウンド終了が検知されないため、復帰動作を開始します。")
                    threading.Thread(target=self._execute_recovery_action, daemon=True).start()

            # --- メイン動作 (Round was valid.) ---
            if found_round:
                if self.is_standby:
                    self.is_standby = False
                    if self.toggles["standby_resume"].get():
                        self.log("【ACTIVE】ラウンド終了を検知しました。スタンバイを解除して稼働を再開します。")
                
                self.last_valid_time = time.time()
                threading.Thread(target=self._execute_main_action, daemon=True).start()

    def _execute_recovery_action(self):
        if not self.action_lock.acquire(blocking=False): return
        try:
            self.log("リカバリー動作(後退)を実行します...")
            pydirectinput.keyDown('s')
            self._safe_sleep(self.time_params["back_time"], self.is_running)
            pydirectinput.keyUp('s')
            self._safe_sleep(0.1, self.is_running)
            
            rec_start = time.time()
            is_right = True
            self.log("リカバリー動作(左右Use連打)を開始します。")
            
            while time.time() - rec_start < self.time_params["max_recovery"] and self.is_running and self.is_standby:
                current_key = 'd' if is_right else 'a'
                pydirectinput.keyDown(current_key)
                
                step_end = time.time() + 3.0
                while time.time() < step_end and self.is_running and self.is_standby:
                    pydirectinput.mouseDown()
                    self._safe_sleep(0.05, self.is_running)
                    pydirectinput.mouseUp()
                    self._safe_sleep(0.1, self.is_running)
                
                pydirectinput.keyUp(current_key)
                is_right = not is_right
                
            self.log("リカバリー動作が終了、または中断されました。")
        finally:
            self._release_all_inputs()
            self.action_lock.release()

    def _execute_main_action(self):
        if not self.action_lock.acquire(blocking=False): return
        try:
            self.log(f"検知: '{self.TARGET_KEYWORD}' -> 自動ボタン押下開始")
            if not self._safe_sleep(self.time_params["wait"], self.is_running): return
            
            # --- パニッシュ検知による1.66倍設定の適用 ---
            multiplier = self.punish_multiplier
            self.punish_multiplier = 1.0
            
            fwd_time = self.time_params["fwd"] * multiplier
            left_time = self.time_params["left"] * multiplier
            
            if multiplier > 1.0:
                self.log(f"【パニッシュ対応】移動時間を {multiplier}倍 にして実行します。")
            
            self.log("前方(W)へ移動")
            pydirectinput.keyDown('w')
            if not self._safe_sleep(fwd_time, self.is_running): return
            pydirectinput.keyUp('w')
            if not self._safe_sleep(0.1, self.is_running): return
            
            self.log("左方(A)へ移動")
            pydirectinput.keyDown('a')
            if not self._safe_sleep(left_time, self.is_running): return
            pydirectinput.keyUp('a')
            if not self._safe_sleep(0.2, self.is_running): return
            
            self.log("オブジェクトをUse (クリック)")
            pydirectinput.mouseDown()
            self._safe_sleep(0.1, self.is_running)
            pydirectinput.mouseUp()
            self.log("自動ボタン押下完了。")

            if self.toggles["speed"].get() and self.is_running:
                self.log("【速度検知】左右移動を開始します...")
                self.osc_vel_x = self.osc_vel_y = self.osc_vel_z = self.osc_vel_mag = 0.0
                
                self.is_testing_speed = True
                self.max_velocity_during_test = 0.0
                
                pydirectinput.keyDown('a')
                if not self._safe_sleep(self.time_params["test_left"], self.is_running): return
                pydirectinput.keyUp('a')
                if not self._safe_sleep(0.1, self.is_running): return
                
                pydirectinput.keyDown('d')
                if not self._safe_sleep(self.time_params["test_right"], self.is_running): return
                pydirectinput.keyUp('d')
                if not self._safe_sleep(0.1, self.is_running): return
                
                self.is_testing_speed = False
                
                if self.max_velocity_during_test == 0.0:
                    self.log("【警告】最大速度が0.0でした。OSCが受信できていない可能性があります。")
                else:
                    self.log(f"検知終了。最大速度: {self.max_velocity_during_test:.3f}")
                
                v_max = self.max_velocity_during_test
                t1 = self.time_params["punish_thresh"]
                t2 = self.time_params["8page_thresh"]
                matched = None
                
                if v_max < t1 and v_max < t2: matched = "punish" if t1 < t2 else "8page"
                elif v_max < t1: matched = "punish"
                elif v_max < t2: matched = "8page"
                
                if matched == "punish":
                    self.log(f"【警告】速度がパニッシュ閾値({t1})未満です。次回メイン動作の移動時間を1.66倍します。")
                    play_alert_sound(self.mp3_punish_var.get().strip())
                    self.punish_multiplier = 1.66
                elif matched == "8page":
                    self.log(f"【警告】速度が8Page閾値({t2})未満です。")
                    play_alert_sound(self.mp3_8page_var.get().strip())
                else:
                    self.log("速度は正常です。")
                    
        finally:
            self.last_valid_time = time.time()
            self._release_all_inputs()
            self.action_lock.release()

    def _osc_worker(self):
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 65536)
        
        try: 
            sock.bind(("0.0.0.0", 9001))
            self.after(1000, lambda: self.log("【OSC】ポート9001での受信待機を開始しました。"))
        except Exception as e: 
            self.after(1000, lambda: self.log(f"【OSCエラー】ポートのバインドに失敗しました。({e})"))
            return
            
        sock.settimeout(0.1)
        first_receive = True
        
        while not self.app_exit_event.is_set():
            try:
                data, _ = sock.recvfrom(65536)
                if first_receive:
                    self.after(0, lambda: self.log("【OSC】VRChatからのOSC初回到達を確認しました。"))
                    first_receive = False
                    
                for addr, val in parse_osc_floats(data):
                    if addr == "/avatar/parameters/VelocityMagnitude":
                        self.osc_vel_mag = val
                        self.osc_last_mag_time = time.time()
                    elif addr == "/avatar/parameters/VelocityX": self.osc_vel_x = val
                    elif addr == "/avatar/parameters/VelocityY": self.osc_vel_y = val
                    elif addr == "/avatar/parameters/VelocityZ": self.osc_vel_z = val
                
                if time.time() - self.osc_last_mag_time < 2.0:
                    self.current_velocity = self.osc_vel_mag
                else:
                    self.current_velocity = math.sqrt(self.osc_vel_x**2 + self.osc_vel_y**2 + self.osc_vel_z**2)
                
                if self.is_testing_speed:
                    self.max_velocity_during_test = max(self.max_velocity_during_test, self.current_velocity)
                    
            except socket.timeout: pass
            except Exception: pass
            
        sock.close()

    # ==========================================
    # 🚀 OTAアップデート & お掃除処理
    # ==========================================
    def _cleanup_old_versions(self):
        if not getattr(sys, 'frozen', False): return
        def cleanup():
            current_exe = os.path.abspath(sys.executable)
            exe_dir = os.path.dirname(current_exe)
            for _ in range(5):
                time.sleep(2.0)
                all_cleaned = True
                for file in glob.glob(os.path.join(exe_dir, "TonButton_Autoclick*.exe")):
                    if os.path.abspath(file) != current_exe:
                        try:
                            os.remove(file)
                            self.log(f"【クリーン】旧バージョンを削除しました: {os.path.basename(file)}")
                        except Exception:
                            all_cleaned = False
                if all_cleaned: break
        threading.Thread(target=cleanup, daemon=True).start()

    def _check_for_updates(self):
        if not getattr(sys, 'frozen', False): return
        threading.Thread(target=self._update_worker, daemon=True).start()

    def _update_worker(self):
        try:
            req = urllib.request.Request(UPDATE_INFO_URL, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=5) as res:
                data = json.loads(res.read().decode('utf-8'))
                
            latest_version = data.get("version")
            download_url = data.get("url")
            release_notes = data.get("release_notes", "システムの最適化と不具合の修正を行いました。")
            
            if latest_version and latest_version != CURRENT_VERSION:
                self.after(0, lambda: self._prompt_update(latest_version, download_url, release_notes))
        except Exception: pass 

    def _prompt_update(self, latest_version, download_url, release_notes):
        msg = f"新しいバージョン (v{latest_version}) が見つかりました。\n\n【アップデート内容】\n{release_notes}\n\n今すぐ自動アップデートしますか？"
        if messagebox.askyesno("アップデート通知", msg):
            self.btn_start.configure(state="disabled")
            self.btn_stop.configure(state="disabled")
            self.log(f"v{latest_version} のダウンロードを開始しました...")
            threading.Thread(target=self._download_and_apply_update, args=(download_url, latest_version), daemon=True).start()

    def _download_and_apply_update(self, download_url, latest_version):
        try:
            current_exe = sys.executable if getattr(sys, 'frozen', False) else os.path.abspath(sys.argv[0])
            exe_dir = os.path.dirname(current_exe)
            new_exe_path = os.path.join(exe_dir, f"TonButton_Autoclick_v{latest_version}.exe")
            
            req = urllib.request.Request(download_url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=60) as res:
                total_size = int(res.headers.get('Content-Length', 0))
                downloaded_size = 0
                with open(new_exe_path, 'wb') as f:
                    while True:
                        chunk = res.read(8192)
                        if not chunk: break
                        f.write(chunk)
                        downloaded_size += len(chunk)
                        
            if total_size > 0 and downloaded_size != total_size:
                raise Exception(f"通信切断 ({downloaded_size}B / {total_size}B)")
                
            self.log("ダウンロード完了。再起動します...")
            os.startfile(new_exe_path)
            self.after(500, self._safe_exit)
            
        except Exception as e:
            self.after(0, lambda: self.log(f"【エラー】アップデート失敗: {e}"))
            self.after(0, lambda: self.btn_start.configure(state="normal"))

    def _on_closing(self):
        self._safe_exit()

    def _safe_exit(self):
        self._save_config()
        self.stop_event.set()
        self.app_exit_event.set()
        self.after(500, self._final_destroy)
        
    def _final_destroy(self):
        self.destroy()
        sys.exit(0)


if __name__ == "__main__":
    app = VRCMacroApp()
    app.mainloop()