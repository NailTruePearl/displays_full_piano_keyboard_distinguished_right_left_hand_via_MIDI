import matplotlib
# 必须在其他matplotlib导入之前设置后端
matplotlib.use('Agg')  # 使用非交互式后端
import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib.patches import Rectangle
import numpy as np
import mido
import time
from collections import defaultdict
from matplotlib.animation import FuncAnimation
import tkinter as tk
from tkinter import filedialog, ttk
import threading
import queue
import warnings

# 设置字体路径
font_path = r"C:\xxxxxxxxxxxxxxxxxxx.ttf"
matplotlib.font_manager.fontManager.addfont(font_path)
font_name = matplotlib.font_manager.FontProperties(fname=font_path).get_name()
plt.rcParams['font.sans-serif'] = [font_name]
plt.rcParams['axes.unicode_minus'] = False


class PianoKeyboard:
    def __init__(self, use_tk_gui=False):
        """初始化钢琴键盘（使用固定参数）
        
        参数:
        use_tk_gui: 是否在Tkinter GUI中使用
        """
        # 缩放比例
        scale = 1.6
        
        # 键的尺寸（单位：mm）
        self.white_key_length = 140 * scale
        self.white_key_width = 22 * scale
        self.black_key_length = 90 * scale
        self.black_key_width = 10 * scale
        self.white_key_gap = 1 * scale  # 白键之间的间隙
        
        # 颜色定义
        self.white_key_color = '#FFFFFF'
        self.black_key_color = '#000000'
        self.white_key_edge = '#000000'
        self.black_key_edge = '#000000'
        self.active_color_right = 'red'    # 右手激活键的颜色
        self.active_color_left = 'green'   # 左手激活键的颜色
        self.inactive_color_white = '#FFFFFF'
        self.inactive_color_black = '#000000'
        
        # 五线谱参数
        self.staff_line_spacing = 7 * scale  # 线间距
        self.staff_line_width = 1 * scale
        self.note_head_width = 6 * scale
        self.note_head_height = 6 * scale
        self.stem_length = 16 * scale  # 符干长度
        
        # 五线谱垂直位置参数
        self.staff_vertical_offset = -190 * scale  # 默认距离琴键-190mm
        
        # 谱号垂直位置参数
        self.clef_vertical_offset = -5 * self.staff_line_spacing  # 默认在五线谱上方-5个线间距
        
        # C4标签位置参数
        self.c4_label_offset = -50 * scale  # 默认在白键顶部上方-50mm
        
        # 英文标题位置参数
        self.english_title_offset = 10  # 默认位置
        
        # 中文标题位置参数
        self.chinese_title_offset = -8 * self.staff_line_spacing  # 默认在五线谱上方-8个线间距
        
        # 白键标签位置参数
        self.white_key_label_offset = 20 * scale  # 默认偏移20
        
        # 黑键标签位置参数
        self.black_key_label_offset = 0 * scale  # 默认不偏移
        
        # 五线谱键位名称显示控制
        self.show_staff_note_labels = False
        
        # 五线谱键位名称垂直偏移
        self.staff_note_label_offset = 0 * scale  # 默认不偏移
        
        # 是否在Tkinter GUI中使用
        self.use_tk_gui = use_tk_gui
        
        if not self.use_tk_gui:
            # 创建独立的matplotlib图形
            self.fig, self.ax = plt.subplots(figsize=(20 * scale, 10 * scale))
        else:
            # 在Tkinter GUI中创建图形
            from matplotlib.figure import Figure
            from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
            self.fig = Figure(figsize=(20 * scale, 10 * scale))
            self.ax = self.fig.add_subplot(111)
        
        # 存储所有键的图形对象
        self.key_patches = []
        # 存储音符名称到矩形对象的映射
        self.key_dict = {}
        
        # 存储五线谱上的音符对象
        self.staff_note_dict = {}
        
        # MIDI数据
        self.midi_notes = []
        self.current_time = 0
        self.is_playing = False
        self.is_paused = False
        self.playback_speed = 1.0
        
        # 播放控制相关
        self.paused_time = 0
        self.actual_start_time = 0
        self.total_duration = 0
        
        # 动画相关
        self.animation = None
        self.animation_thread = None
        self.stop_animation_flag = False
        
        # 设置保存路径
        self.save_path = r"D:\xxxxxxxxxxxxx.png"
        
        # 事件队列，用于线程间通信
        self.event_queue = queue.Queue()
        
        self.setup_keyboard()
        
        if not self.use_tk_gui:
            # 连接关闭事件
            self.fig.canvas.mpl_connect('close_event', self.on_close)
    
    def setup_keyboard(self):
        """设置键盘布局"""
        # 清空图形
        self.ax.clear()
        
        # 清空存储的键和音符
        self.key_patches = []
        self.key_dict = {}
        self.staff_note_dict = {}
        
        # 绘制最左边的三个键（A0, A#0, B0）
        last_x = self.draw_left_three_keys()
        
        # 绘制中间7个完整的八度（从C1到B7）
        octave_start_x = last_x + self.white_key_gap
        
        # 7个完整的八度
        for octave in range(1, 8):  # octave从1到7
            octave_x = octave_start_x + (octave - 1) * 7 * (self.white_key_width + self.white_key_gap)
            self.draw_octave(octave, octave_x)
        
        # 绘制最右边的一个白键（C8）
        last_x = octave_start_x + 7 * 7 * (self.white_key_width + self.white_key_gap)
        self.draw_single_white_key(8, last_x)
        
        # 计算总宽度
        total_width = last_x + self.white_key_width
        
        # 绘制合并后的五线谱系统（C2到B5）
        self.draw_merged_staff_system(octave_start_x)
        
        # 设置图形属性
        self.ax.set_xlim(-10, total_width + 10)
        self.ax.set_ylim(-200, self.white_key_length + 100)
        self.ax.set_aspect('equal')
        self.ax.axis('off')
        
        # 添加英文标题
        title_y = self.white_key_length + 20 * self.white_key_width/22 + self.english_title_offset
        self.ax.text(
            total_width/2,
            title_y,
            '88-Key Piano Keyboard (A0 to C8) with Staff Notation',
            ha='center',
            va='bottom',
            fontsize=14 * self.white_key_width/22,
            fontweight='bold'
        )
        
        if self.use_tk_gui:
            # 在Tkinter中绘制
            self.fig.tight_layout()
    
    def draw_left_three_keys(self):
        """绘制最左边的三个键（A0, A#0, B0）"""
        x_pos = 0
        
        # 第一个白键 A0
        self.draw_white_key(0, 'A', x_pos, is_leftmost=True)
        
        # 第二个白键 B0 - 需要在A0右边留出间隙
        b0_x_pos = x_pos + self.white_key_width + self.white_key_gap
        self.draw_white_key(0, 'B', b0_x_pos, is_leftmost=True)
        
        # 黑键 A#0 - 位于A0和B0之间正中间
        a0_right = x_pos + self.white_key_width
        b0_left = b0_x_pos
        black_center = (a0_right + b0_left) / 2
        black_x = black_center - self.black_key_width / 2
        self.draw_black_key(0, 'A#', black_x)
        
        # 返回B0的右边界位置
        return b0_x_pos + self.white_key_width
    
    def draw_octave(self, octave_num, start_x):
        """
        绘制一个完整的八度
        
        参数:
        octave_num: 八度编号 (1-7)
        start_x: 起始x坐标
        """
        # 八度内的白键名称
        white_key_names = ['C', 'D', 'E', 'F', 'G', 'A', 'B']
        
        # 黑键配置：每个位置是否有黑键，以及黑键名称
        black_key_config = [
            (True, 'C#'),    # C和D之间
            (True, 'D#'),    # D和E之间
            (False, ''),     # E和F之间没有黑键
            (True, 'F#'),    # F和G之间
            (True, 'G#'),    # G和A之间
            (True, 'A#'),    # A和B之间
            (False, '')      # B和下一个C之间没有黑键
        ]
        
        x_pos = start_x
        
        # 先绘制白键，同时收集白键的位置信息
        white_key_positions = []
        for i, note in enumerate(white_key_names):
            # 绘制白键
            self.draw_white_key(octave_num, note, x_pos)
            white_key_positions.append(x_pos)
            x_pos += self.white_key_width + self.white_key_gap
        
        # 然后绘制黑键，确保黑键在两个白键的正中间
        for i in range(len(white_key_names) - 1):
            if black_key_config[i][0]:
                # 计算黑键应该在的位置：两个白键的正中间
                current_key_right = white_key_positions[i] + self.white_key_width
                next_key_left = white_key_positions[i+1]
                black_center = (current_key_right + next_key_left) / 2
                black_x = black_center - self.black_key_width / 2
                
                black_note = black_key_config[i][1]
                self.draw_black_key(octave_num, black_note, black_x)
    
    def draw_single_white_key(self, octave_num, x_pos):
        """绘制单个白键（最右边，C8）"""
        note_name = f"C{octave_num}"
        rect = Rectangle(
            (x_pos, 0), 
            self.white_key_width, 
            self.white_key_length,
            facecolor=self.white_key_color,
            edgecolor=self.white_key_edge,
            linewidth=1
        )
        self.ax.add_patch(rect)
        
        # 添加标签 C8
        self.ax.text(
            x_pos + self.white_key_width/2,
            -5 + self.white_key_label_offset,
            note_name,
            ha='center',
            va='top',
            fontsize=8 * self.white_key_width/22,
        )
        
        # 保存引用
        self.key_patches.append(rect)
        self.key_dict[note_name] = rect
    
    def draw_white_key(self, octave_num, note, x_pos, is_leftmost=False):
        """
        绘制白键
        
        参数:
        octave_num: 八度编号
        note: 音名
        x_pos: x坐标
        is_leftmost: 是否为最左边的键
        """
        # 绘制白键矩形
        if is_leftmost and octave_num == 0:
            note_name = f"{note}{octave_num}"
        else:
            note_name = f"{note}{octave_num}"
        
        rect = Rectangle(
            (x_pos, 0), 
            self.white_key_width, 
            self.white_key_length,
            facecolor=self.white_key_color,
            edgecolor=self.white_key_edge,
            linewidth=1
        )
        self.ax.add_patch(rect)
        
        # 添加标签
        self.ax.text(
            x_pos + self.white_key_width/2,
            -5 + self.white_key_label_offset,
            note_name,
            ha='center',
            va='top',
            fontsize=8 * self.white_key_width/22
        )
        
        # 标记中央C (C4)
        if note_name == "C4":
            self.ax.text(
                x_pos + self.white_key_width/2,
                self.white_key_length + self.c4_label_offset,
                "C4",
                ha='center',
                va='bottom',
                fontsize=7 * self.white_key_width/22,
                fontweight='bold',
                color='red'
            )
        
        # 保存引用
        self.key_patches.append(rect)
        self.key_dict[note_name] = rect
    
    def draw_black_key(self, octave_num, note, x_pos):
        """
        绘制黑键
        
        参数:
        octave_num: 八度编号
        note: 音名
        x_pos: x坐标
        """
        if not note:  # 跳过空的音名
            return
            
        note_name = f"{note}{octave_num}"
        # 绘制黑键矩形
        rect = Rectangle(
            (x_pos, self.white_key_length - self.black_key_length), 
            self.black_key_width, 
            self.black_key_length,
            facecolor=self.black_key_color,
            edgecolor=self.black_key_edge,
            linewidth=1
        )
        self.ax.add_patch(rect)
        
        # 添加标签（如果音名不为空）
        self.ax.text(
            x_pos + self.black_key_width/2,
            self.white_key_length - self.black_key_length - 5 + self.black_key_label_offset,
            note_name,
            ha='center',
            va='top',
            fontsize=7 * self.white_key_width/22,
            color='green'
        )
        
        # 保存引用
        self.key_patches.append(rect)
        self.key_dict[note_name] = rect
    
    def draw_merged_staff_system(self, octave_start_x):
        """
        绘制合并后的五线谱系统（C2到B5）
        """
        # 五线谱范围：C2到B5
        staff_start_octave = 2
        staff_end_octave = 5
        
        # 计算五线谱的x坐标范围
        staff_x_start = octave_start_x + (staff_start_octave - 1) * 7 * (self.white_key_width + self.white_key_gap)
        staff_x_end = octave_start_x + (staff_end_octave) * 7 * (self.white_key_width + self.white_key_gap)
        
        # 五线谱高度
        staff_y_position = self.white_key_length + self.staff_vertical_offset
        
        # 绘制合并后的五线谱
        self.draw_merged_staff_with_notes(staff_x_start, staff_x_end, staff_y_position, 
                                         staff_start_octave, staff_end_octave)
    
    def draw_merged_staff_with_notes(self, start_x, end_x, staff_height, start_octave, end_octave):
        """
        绘制合并后的五线谱和音符
        
        参数:
        start_x: 起始x坐标
        end_x: 结束x坐标
        staff_height: 五线谱底部第一条线的高度
        start_octave: 起始八度
        end_octave: 结束八度
        """
        # 绘制五条主线
        for i in range(5):
            y_pos = staff_height + i * self.staff_line_spacing
            self.ax.hlines(
                y=y_pos,
                xmin=start_x,
                xmax=end_x,
                color='red',
                linewidth=self.staff_line_width
            )
        
        # 绘制拓展线
        # 下方2条拓展线（用于低音谱表）
        for i in range(1, 3):
            y_pos = staff_height - i * self.staff_line_spacing
            self.ax.hlines(
                y=y_pos,
                xmin=start_x,
                xmax=end_x,
                color='black',
                linewidth=self.staff_line_width,
                linestyle='--'
            )
        
        # 上方1条拓展线（用于高音谱表）
        y_pos = staff_height + 5 * self.staff_line_spacing
        self.ax.hlines(
            y=y_pos,
            xmin=start_x,
            xmax=end_x,
            color='black',
            linewidth=self.staff_line_width,
            linestyle='--'
        )
        
        # 绘制谱号
        # 在C2的位置绘制低音谱号，C4的位置绘制高音谱号
        # 计算C2和C4的x坐标
        white_key_names = ['C', 'D', 'E', 'F', 'G', 'A', 'B']
        
        # 计算谱号位置
        c2_x = start_x + white_key_names.index('C') * (self.white_key_width + self.white_key_gap) + self.white_key_width/2
        c4_x = start_x + (4 - start_octave) * 7 * (self.white_key_width + self.white_key_gap) + white_key_names.index('C') * (self.white_key_width + self.white_key_gap) + self.white_key_width/2
        
        # 绘制谱号字母
        # 低音谱号 (F)
        clef_F_y = staff_height + self.clef_vertical_offset
        self.ax.text(c2_x, clef_F_y, "F", 
                    ha='center', va='center', fontsize=16, fontweight='bold',color='red')
        
        # 高音谱号 (G)
        clef_G_y = staff_height + self.clef_vertical_offset
        self.ax.text(c4_x, clef_G_y, "G", 
                    ha='center', va='center', fontsize=16, fontweight='bold',color='red')
        
        # 绘制所有音符（C2到B5）
        for octave in range(start_octave, end_octave + 1):
            for i, note in enumerate(white_key_names):
                # 计算x坐标
                octave_offset = (octave - start_octave) * 7 * (self.white_key_width + self.white_key_gap)
                key_offset = i * (self.white_key_width + self.white_key_gap)
                x_pos = start_x + octave_offset + key_offset + self.white_key_width/2
                
                # 根据八度决定使用哪种规则
                if octave <= 3:
                    # 使用低音谱表规则（八度2-3）
                    if octave == 2:
                        note_index = white_key_names.index(note)
                        y_offset = -2 * self.staff_line_spacing + note_index * (self.staff_line_spacing / 2)
                    elif octave == 3:
                        note_index = white_key_names.index(note)
                        y_offset = 1.5 * self.staff_line_spacing + note_index * (self.staff_line_spacing / 2)
                    else:
                        y_offset = 0
                else:
                    # 使用高音谱表规则（八度4-5）
                    if octave == 4:
                        note_index = white_key_names.index(note)
                        y_offset = -self.staff_line_spacing + note_index * (self.staff_line_spacing / 2)
                    elif octave == 5:
                        note_index = white_key_names.index(note)
                        y_offset = 2.5 * self.staff_line_spacing + note_index * (self.staff_line_spacing / 2)
                    else:
                        y_offset = 0
                
                # 计算y坐标
                y_pos = staff_height + y_offset
                
                # 创建音符名（用于存储和查找）
                note_name = f"{note}{octave}"
                
                # 绘制音符头（椭圆）
                note_head = patches.Ellipse(
                    (x_pos, y_pos),
                    width=self.note_head_width,
                    height=self.note_head_height,
                    facecolor='black',
                    edgecolor='black'
                )
                self.ax.add_patch(note_head)
                
                # 绘制符干
                stem_line = None
                if octave <= 3:
                    # 低音谱表：符干向上
                    stem_x = x_pos + self.note_head_width/2 - 0
                    stem_line, = self.ax.plot([stem_x, stem_x], [y_pos, y_pos + self.stem_length], 
                                            'k-', linewidth=1.5)
                else:
                    # 高音谱表：根据音符位置决定符干方向
                    if y_offset < 2 * self.staff_line_spacing:  # 第三线以下
                        stem_x = x_pos + self.note_head_width/2 - 0
                        stem_line, = self.ax.plot([stem_x, stem_x], [y_pos, y_pos + self.stem_length], 
                                                'k-', linewidth=1.5)
                    else:  # 第三线以上
                        stem_x = x_pos - self.note_head_width/2 + 0
                        stem_line, = self.ax.plot([stem_x, stem_x], [y_pos, y_pos - self.stem_length], 
                                                'k-', linewidth=1.5)
                
                # 存储音符头和符干
                if stem_line:
                    self.staff_note_dict[note_name] = {
                        'note_head': note_head,
                        'stem': stem_line
                    }
                else:
                    self.staff_note_dict[note_name] = {
                        'note_head': note_head,
                        'stem': None
                    }
        
        # 添加合并后的五线谱标题
        chinese_title_y = staff_height + self.chinese_title_offset
        self.ax.text(start_x + (end_x - start_x)/2, chinese_title_y,
                    f"五线谱 (C{start_octave}-B{end_octave})", 
                    ha='center', va='bottom', fontsize=10, fontweight='bold')
    
    def load_midi_file(self, filepath):
        """
        加载并解析MIDI文件
        
        参数:
        filepath: MIDI文件路径
        """
        try:
            # 使用mido库读取MIDI文件
            midi_file = mido.MidiFile(filepath)
            
            # 清空之前的MIDI数据
            self.midi_notes = []
            
            print(f"成功加载MIDI文件: {filepath}")
            print(f"MIDI文件格式: {midi_file.type}")
            print(f"曲目数: {len(midi_file.tracks)}")
            print(f"每四分音符的微秒数: {midi_file.ticks_per_beat}")
            
            # 存储音符事件
            current_time = 0  # 以tick为单位
            active_notes = {}  # 存储正在播放的音符，键为音高，值为开始时间和通道
            
            # 解析所有轨道
            for i, track in enumerate(midi_file.tracks):
                print(f"\n轨道 {i}: {track.name}")
                
                track_time = 0
                for msg in track:
                    track_time += msg.time
                    
                    # 检查消息是否有通道属性
                    channel = getattr(msg, 'channel', 0) + 1  # MIDI通道从1开始，mido使用0-15
                    
                    if msg.type == 'note_on' and msg.velocity > 0:
                        # 音符开始
                        active_notes[msg.note] = (track_time, channel)
                    elif msg.type == 'note_off' or (msg.type == 'note_on' and msg.velocity == 0):
                        # 音符结束
                        if msg.note in active_notes:
                            start_time, note_channel = active_notes[msg.note]
                            duration = track_time - start_time
                            
                            # 将MIDI音高转换为音符名
                            note_name = self.midi_note_to_name(msg.note)
                            
                            if note_name:
                                # 将时间转换为秒（简化处理）
                                # 实际应该根据tempo事件来计算
                                start_sec = start_time / midi_file.ticks_per_beat
                                end_sec = track_time / midi_file.ticks_per_beat
                                
                                self.midi_notes.append({
                                    'note': note_name,
                                    'midi_note': msg.note,
                                    'start': start_sec,
                                    'end': end_sec,
                                    'duration': duration / midi_file.ticks_per_beat,
                                    'velocity': msg.velocity if hasattr(msg, 'velocity') else 64,
                                    'channel': note_channel  # 添加通道信息
                                })
                            
                            # 从活跃音符中移除
                            del active_notes[msg.note]
            
            # 按开始时间排序
            self.midi_notes.sort(key=lambda x: x['start'])
            
            # 计算总时长
            if self.midi_notes:
                self.total_duration = max(note['end'] for note in self.midi_notes)
                print(f"\n解析完成！共找到 {len(self.midi_notes)} 个音符事件")
                print(f"总时长: {self.total_duration:.2f} 拍")
                
                # 统计音符频率
                note_count = {}
                channel_count = {}
                for note in self.midi_notes:
                    if note['note'] in note_count:
                        note_count[note['note']] += 1
                    else:
                        note_count[note['note']] = 1
                    
                    # 统计通道使用情况
                    channel = note['channel']
                    if channel in channel_count:
                        channel_count[channel] += 1
                    else:
                        channel_count[channel] = 1
                
                print("\n最常见的10个音符:")
                sorted_notes = sorted(note_count.items(), key=lambda x: x[1], reverse=True)
                for note, count in sorted_notes[:10]:
                    print(f"  {note}: {count}次")
                
                print("\n通道使用情况:")
                for channel, count in sorted(channel_count.items()):
                    hand = "右手" if channel == 1 else "左手" if channel == 5 else "未知"
                    print(f"  通道 {channel} ({hand}): {count}个音符")
            
            return True
            
        except Exception as e:
            print(f"加载MIDI文件时出错: {e}")
            return False
    
    def midi_note_to_name(self, midi_note):
        """
        将MIDI音高转换为音符名称
        
        参数:
        midi_note: MIDI音高值 (0-127)
        
        返回:
        音符名称字符串，如 "C4", "A#5" 等
        """
        # MIDI音高21对应A0，108对应C8
        if midi_note < 21 or midi_note > 108:
            return None
        
        # 音符名称映射
        note_names = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']
        
        # 计算八度和音符索引
        octave = (midi_note - 12) // 12
        note_index = midi_note % 12
        
        # 获取音符名称
        note_name = note_names[note_index]
        
        # 对于黑键（升降号），使用#表示
        if '#' in note_name:
            return f"{note_name}{octave}"
        else:
            return f"{note_name}{octave}"
    
    def activate_key(self, note_name, channel=1):
        """
        激活指定的键
        
        参数:
        note_name: 音符名称，如 "C4", "A#5"
        channel: MIDI通道，1为右手(红色)，5为左手(绿色)
        """
        # 根据通道选择颜色
        if channel == 5:  # 左手
            active_color = self.active_color_left
        else:  # 默认或右手
            active_color = self.active_color_right
        
        # 激活琴键
        if note_name in self.key_dict:
            rect = self.key_dict[note_name]
            rect.set_facecolor(active_color)
            rect.set_edgecolor(active_color)
        
        # 激活五线谱上的音符（如果存在）
        if note_name in self.staff_note_dict:
            note_data = self.staff_note_dict[note_name]
            note_data['note_head'].set_facecolor(active_color)
            note_data['note_head'].set_edgecolor(active_color)
            
            if note_data['stem']:
                note_data['stem'].set_color(active_color)
    
    def deactivate_key(self, note_name):
        """
        取消激活指定的键（恢复原色）
        
        参数:
        note_name: 音符名称，如 "C4", "A#5"
        """
        # 判断是白键还是黑键
        is_black_key = '#' in note_name
        
        # 恢复琴键颜色
        if note_name in self.key_dict:
            rect = self.key_dict[note_name]
            if is_black_key:
                rect.set_facecolor(self.black_key_color)
                rect.set_edgecolor(self.black_key_edge)
            else:
                rect.set_facecolor(self.white_key_color)
                rect.set_edgecolor(self.white_key_edge)
        
        # 恢复五线谱上的音符颜色（如果存在）
        if note_name in self.staff_note_dict:
            note_data = self.staff_note_dict[note_name]
            note_data['note_head'].set_facecolor('black')
            note_data['note_head'].set_edgecolor('black')
            
            if note_data['stem']:
                note_data['stem'].set_color('black')
    
    def reset_all_keys(self):
        """重置所有键的颜色"""
        # 重置所有琴键
        for note_name, rect in self.key_dict.items():
            is_black_key = '#' in note_name
            if is_black_key:
                rect.set_facecolor(self.black_key_color)
                rect.set_edgecolor(self.black_key_edge)
            else:
                rect.set_facecolor(self.white_key_color)
                rect.set_edgecolor(self.white_key_edge)
        
        # 重置所有五线谱音符
        for note_name, note_data in self.staff_note_dict.items():
            note_data['note_head'].set_facecolor('black')
            note_data['note_head'].set_edgecolor('black')
            if note_data['stem']:
                note_data['stem'].set_color('black')
    
    def update_animation(self, current_time=None):
        """
        更新动画帧
        
        参数:
        current_time: 指定当前时间，如果为None则计算时间
        """
        if not self.midi_notes:
            return
        
        # 重置所有键的颜色
        self.reset_all_keys()
        
        # 计算当前时间
        if current_time is None:
            if self.is_paused:
                current_time = self.paused_time
            else:
                current_time = (time.time() - self.actual_start_time) * self.playback_speed + self.start_time
        
        self.current_time = current_time
        
        # 激活当前时间正在弹奏的键
        active_notes = []
        for note in self.midi_notes:
            # 如果音符在当前时间范围内
            if note['start'] <= current_time <= note['end']:
                self.activate_key(note['note'], note.get('channel', 1))
                active_notes.append(note['note'])
        
        # 更新图形
        if self.use_tk_gui:
            self.fig.canvas.draw_idle()
        else:
            self.fig.canvas.draw()
        
        # 检查是否应该停止动画
        if self.stop_animation_flag:
            return False
        
        # 检查是否到达结束时间
        if current_time > self.total_duration:
            return False
        
        return True
    
    def animation_loop(self):
        """动画循环"""
        interval = 1  # 毫秒 - 提高时间精度到1毫秒
        
        while not self.stop_animation_flag:
            if not self.update_animation():
                break
            
            # 等待下一帧
            time.sleep(interval / 1000.0)
        
        # 动画结束，重置标志
        self.stop_animation_flag = False
        self.is_playing = False
        self.is_paused = False
    
    def start_animation(self, tk_window=None, start_time=0):
        """开始播放动画

        参数:
        tk_window: 在Tkinter模式下，需要传入Tkinter主窗口对象
        start_time: 开始播放的时间位置
        """
        if not self.midi_notes:
            print("没有加载MIDI文件，请先加载MIDI文件")
            return

        # 停止之前的动画
        self.stop_animation()

        # 重置所有键
        self.reset_all_keys()

        print(f"开始播放动画，总时长: {self.total_duration:.2f}秒")
        print(f"播放速度: {self.playback_speed}x")
        print(f"开始时间: {start_time:.2f}秒")

        # 设置动画开始时间和起始时间
        self.start_time = start_time
        self.actual_start_time = time.time()
        self.is_playing = True
        self.is_paused = False
        self.stop_animation_flag = False

        if self.use_tk_gui:
            # 在Tkinter中，我们需要通过Tkinter主窗口的after方法来调度
            # 保存对Tkinter窗口的引用
            self.tk_window = tk_window
            
            def tk_animation_update():
                if not self.stop_animation_flag and self.is_playing and not self.is_paused:
                    if not self.update_animation():
                        # 播放结束
                        self.is_playing = False
                        self.is_paused = False
                        return
                    
                    # 继续下一次更新，使用1毫秒间隔
                    self.tk_window.after(1, tk_animation_update)
            
            # 启动动画
            self.tk_window.after(0, tk_animation_update)
        else:
            # 在独立窗口中，使用线程运行动画
            self.animation_thread = threading.Thread(target=self.animation_loop, daemon=True)
            self.animation_thread.start()
            
            # 显示窗口（非阻塞）
            if not plt.fignum_exists(self.fig.number):
                plt.show(block=False)
    
    def pause_animation(self):
        """暂停动画"""
        if self.is_playing and not self.is_paused:
            self.is_paused = True
            self.paused_time = self.current_time
            print(f"动画已暂停，当前时间: {self.paused_time:.2f}秒")
    
    def resume_animation(self):
        """继续动画"""
        if self.is_playing and self.is_paused:
            self.is_paused = False
            # 重新计算开始时间，使得从暂停的位置继续
            self.actual_start_time = time.time() - self.paused_time / self.playback_speed
            self.start_time = 0  # 重置start_time，因为paused_time已经是绝对时间
            print(f"动画已继续，从时间: {self.paused_time:.2f}秒")
            
            if self.use_tk_gui and self.tk_window:
                # 重新启动Tkinter动画更新
                def tk_animation_update():
                    if not self.stop_animation_flag and self.is_playing and not self.is_paused:
                        if not self.update_animation():
                            # 播放结束
                            self.is_playing = False
                            self.is_paused = False
                            return
                        
                        # 继续下一次更新
                        self.tk_window.after(1, tk_animation_update)
                
                self.tk_window.after(0, tk_animation_update)
    
    def stop_animation(self):
        """停止播放动画并回到开头"""
        self.stop_animation_flag = True
        self.is_playing = False
        self.is_paused = False
        self.current_time = 0
        
        # 重置所有键的颜色
        self.reset_all_keys()
        
        if self.animation_thread and self.animation_thread.is_alive():
            self.animation_thread.join(timeout=1.0)
    
    def seek_to_position(self, position):
        """跳转到指定位置
        
        参数:
        position: 位置（秒）
        """
        # 停止当前动画
        self.stop_animation()
        
        # 确保位置在有效范围内
        position = max(0, min(position, self.total_duration))
        
        # 更新到指定位置
        self.update_animation(position)
        
        print(f"已跳转到位置: {position:.2f}秒")
    
    def on_close(self, event):
        """处理窗口关闭事件"""
        self.stop_animation()
    
    def save_image(self, filename=None, dpi=300):
        """保存图像到文件"""
        if filename is None:
            filename = self.save_path
        
        self.fig.savefig(filename, dpi=dpi, bbox_inches='tight', pad_inches=0.5)
        print(f"图像已保存为 {filename}")
    
    def show(self):
        """显示钢琴键盘"""
        if not self.use_tk_gui:
            plt.tight_layout()
            plt.show()


class MIDIVisualizer:
    """MIDI可视化器，提供GUI界面"""
    
    def __init__(self):
        self.piano = None
        self.window = None
        self.canvas = None
        self.animation_id = None
        self.is_paused = False
        self.progress_var = None
        self.progress_scale = None
        self.current_time_label = None
        self.total_time_label = None
        
    def create_gui(self):
        """创建GUI界面"""
        # 创建主窗口
        self.window = tk.Tk()
        self.window.title("MIDI钢琴可视化学习工具 - 左手绿色，右手红色")
        self.window.geometry("1100x900")
        
        # 设置窗口关闭事件
        self.window.protocol("WM_DELETE_WINDOW", self.on_closing)
        
        # 创建框架
        top_frame = tk.Frame(self.window)
        top_frame.pack(side="top", fill="x", padx=10, pady=5)
        
        # 标题
        title_label = tk.Label(top_frame, text="MIDI钢琴可视化学习工具", 
                              font=("Arial", 16, "bold"))
        title_label.pack(pady=10)
        
        # 手部颜色说明
        color_info_frame = tk.Frame(top_frame)
        color_info_frame.pack(pady=5)
        
        right_hand_label = tk.Label(color_info_frame, text="右手(通道1): 红色", 
                                   font=("Arial", 10), fg="red")
        right_hand_label.pack(side="left", padx=10)
        
        left_hand_label = tk.Label(color_info_frame, text="左手(通道5): 绿色", 
                                  font=("Arial", 10), fg="green")
        left_hand_label.pack(side="left", padx=10)
        
        # 控制按钮框架
        control_frame = tk.Frame(top_frame)
        control_frame.pack(pady=10)
        
        # 加载MIDI文件按钮
        load_button = tk.Button(control_frame, text="加载MIDI文件", 
                               command=self.load_midi_file, 
                               font=("Arial", 12), bg="#4CAF50", fg="white",
                               height=2, width=15)
        load_button.pack(side="left", padx=5)
        
        self.play_button = tk.Button(control_frame, text="开始播放", 
                                    command=self.start_playback,
                                    font=("Arial", 12), bg="#2196F3", fg="white",
                                    height=2, width=15, state="disabled")
        self.play_button.pack(side="left", padx=5)
        
        self.pause_button = tk.Button(control_frame, text="暂停", 
                                     command=self.pause_playback,
                                     font=("Arial", 12), bg="#FF9800", fg="white",
                                     height=2, width=15, state="disabled")
        self.pause_button.pack(side="left", padx=5)
        
        self.stop_button = tk.Button(control_frame, text="停止", 
                                    command=self.stop_playback,
                                    font=("Arial", 12), bg="#f44336", fg="white",
                                    height=2, width=15, state="disabled")
        self.stop_button.pack(side="left", padx=5)
        
        self.reset_button = tk.Button(control_frame, text="重置视图", 
                                     command=self.reset_view,
                                     font=("Arial", 12), bg="#9C27B0", fg="white",
                                     height=2, width=15)
        self.reset_button.pack(side="left", padx=5)
        
        # 播放速度控制
        speed_frame = tk.Frame(top_frame)
        speed_frame.pack(pady=10)
        
        speed_label = tk.Label(speed_frame, text="播放速度:", font=("Arial", 12))
        speed_label.pack(side="left", padx=5)
        
        self.speed_var = tk.DoubleVar(value=1.0)
        # 扩展速度范围到0.01-2.0
        speed_scale = tk.Scale(speed_frame, from_=0.01, to=2.0, 
                              resolution=0.01, orient="horizontal",
                              variable=self.speed_var, length=300,
                              command=self.update_speed)
        speed_scale.pack(side="left", padx=5)
        
        # 速度值显示标签
        self.speed_label = tk.Label(speed_frame, text="1.00x", 
                                   font=("Arial", 10), width=8)
        self.speed_label.pack(side="left", padx=5)
        
        # 进度条框架
        progress_frame = tk.Frame(top_frame)
        progress_frame.pack(pady=10, fill="x")
        
        # 当前时间标签
        self.current_time_label = tk.Label(progress_frame, text="00:00.000", 
                                          font=("Arial", 10), width=12)
        self.current_time_label.pack(side="left", padx=5)
        
        # 进度条
        self.progress_var = tk.DoubleVar(value=0)
        # 设置进度条为总毫秒数，精度为5毫秒
        self.progress_scale = tk.Scale(progress_frame, from_=0, to=1000, 
                                      variable=self.progress_var, 
                                      orient="horizontal", length=700,
                                      resolution=0.005,  # 5毫秒精度
                                      command=self.on_progress_change)
        self.progress_scale.pack(side="left", fill="x", expand=True, padx=5)
        self.progress_scale.config(state="disabled")
        
        # 绑定进度条拖动事件
        self.progress_scale.bind("<ButtonPress-1>", self.on_progress_press)
        self.progress_scale.bind("<ButtonRelease-1>", self.on_progress_release)
        
        # 总时间标签
        self.total_time_label = tk.Label(progress_frame, text="00:00.000", 
                                        font=("Arial", 10), width=12)
        self.total_time_label.pack(side="left", padx=5)
        
        # 状态显示
        self.status_label = tk.Label(top_frame, text="等待加载MIDI文件...", 
                                    font=("Arial", 10), fg="blue")
        self.status_label.pack(pady=10)
        
        # 初始化钢琴键盘
        from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
        self.piano = PianoKeyboard(use_tk_gui=True)
        
        # 创建Matplotlib画布
        self.canvas = FigureCanvasTkAgg(self.piano.fig, master=self.window)
        self.canvas.draw()
        self.canvas.get_tk_widget().pack(side="top", fill="both", expand=True, padx=10, pady=10)
        
        # 添加工具栏
        toolbar = NavigationToolbar2Tk(self.canvas, self.window)
        toolbar.update()
        self.canvas.get_tk_widget().pack(side="top", fill="both", expand=True)
        
        # 退出按钮
        exit_button = tk.Button(top_frame, text="退出程序", 
                               command=self.on_closing,
                               font=("Arial", 10), bg="#9E9E9E", fg="white",
                               height=2, width=15)
        exit_button.pack(pady=10)
        
        # 启动进度更新循环
        self.update_progress_loop()
        
        # 运行GUI
        self.window.mainloop()
    
    def update_progress_loop(self):
        """更新进度条循环"""
        if self.piano and self.piano.is_playing and not self.piano.is_paused:
            # 计算当前进度百分比（基于毫秒）
            if self.piano.total_duration > 0:
                # 更新进度条
                current_ms = self.piano.current_time * 1000  # 转换为毫秒
                total_ms = self.piano.total_duration * 1000  # 转换为毫秒
                self.progress_var.set(min(current_ms, total_ms))
                
                # 更新时间标签
                current_time_str = self.format_time_ms(self.piano.current_time)
                self.current_time_label.config(text=current_time_str)
        
        # 每1ms更新一次，提高时间精度
        self.window.after(1, self.update_progress_loop)
    
    def format_time(self, seconds):
        """格式化时间为分:秒格式"""
        minutes = int(seconds // 60)
        secs = int(seconds % 60)
        return f"{minutes:02d}:{secs:02d}"
    
    def format_time_ms(self, seconds):
        """格式化时间为分:秒.毫秒格式"""
        minutes = int(seconds // 60)
        secs = int(seconds % 60)
        ms = int((seconds - int(seconds)) * 1000)
        return f"{minutes:02d}:{secs:02d}.{ms:03d}"
    
    def load_midi_file(self):
        """加载MIDI文件"""
        filepath = filedialog.askopenfilename(
            title="选择MIDI文件",
            filetypes=[("MIDI文件", "*.mid *.midi"), ("所有文件", "*.*")]
        )
        
        if filepath:
            self.status_label.config(text=f"正在加载: {filepath}", fg="blue")
            self.window.update()
            
            # 加载MIDI文件
            success = self.piano.load_midi_file(filepath)
            
            if success:
                self.status_label.config(text=f"成功加载MIDI文件: {filepath}", fg="green")
                self.play_button.config(state="normal")
                self.stop_button.config(state="disabled")
                self.pause_button.config(state="disabled")
                
                # 设置进度条范围为总毫秒数
                total_ms = self.piano.total_duration * 1000
                self.progress_scale.config(to=total_ms, state="normal", resolution=0.005)  # 5毫秒精度
                self.progress_var.set(0)
                
                # 更新时间标签
                total_time_str = self.format_time_ms(self.piano.total_duration)
                self.total_time_label.config(text=total_time_str)
                self.current_time_label.config(text="00:00.000")
                
                # 重新绘制画布
                self.canvas.draw()
            else:
                self.status_label.config(text="加载MIDI文件失败", fg="red")
    
    def start_playback(self):
        """开始播放"""
        if self.piano and self.piano.midi_notes:
            # 获取当前进度位置（毫秒转换为秒）
            start_time = self.progress_var.get() / 1000
            
            self.status_label.config(text="正在播放...", fg="green")
            self.play_button.config(state="disabled")
            self.pause_button.config(state="normal")
            self.stop_button.config(state="normal")
            self.window.update()
            
            # 设置播放速度
            self.piano.playback_speed = self.speed_var.get()
            
            # 开始动画，传入Tkinter主窗口和开始时间
            self.piano.start_animation(self.window, start_time)
    
    def pause_playback(self):
        """暂停/继续播放"""
        if self.piano:
            if self.piano.is_paused:
                # 继续播放
                self.piano.resume_animation()
                self.status_label.config(text="正在播放...", fg="green")
                self.pause_button.config(text="暂停")
                self.play_button.config(state="disabled")
            else:
                # 暂停播放
                self.piano.pause_animation()
                self.status_label.config(text="已暂停", fg="orange")
                self.pause_button.config(text="继续")
                self.play_button.config(state="normal")
    
    def stop_playback(self):
        """停止播放并回到开头"""
        if self.piano:
            self.piano.stop_animation()
            self.status_label.config(text="播放已停止", fg="orange")
            self.play_button.config(state="normal")
            self.pause_button.config(state="disabled")
            self.stop_button.config(state="disabled")
            self.pause_button.config(text="暂停")
            
            # 重置进度条到开头
            self.progress_var.set(0)
            self.current_time_label.config(text="00:00.000")
            
            # 更新画布
            self.canvas.draw()
    
    def reset_view(self):
        """重置视图"""
        if self.piano:
            self.piano.reset_all_keys()
            self.canvas.draw()
            self.status_label.config(text="视图已重置", fg="blue")
    
    def update_speed(self, value):
        """更新播放速度"""
        if self.piano:
            speed = float(value)
            self.piano.playback_speed = speed
            self.speed_label.config(text=f"{speed:.2f}x")
            self.status_label.config(text=f"播放速度: {speed:.2f}x", fg="purple")
    
    def on_progress_change(self, value):
        """进度条变化时的回调函数"""
        # 只在用户拖动进度条时更新显示的时间
        if hasattr(self, 'is_dragging') and self.is_dragging:
            current_ms = float(value)
            current_time_str = self.format_time_ms(current_ms / 1000)
            self.current_time_label.config(text=current_time_str)
    
    def on_progress_press(self, event):
        """进度条按下时"""
        self.is_dragging = True
        # 如果正在播放，暂停播放以便拖动
        if self.piano and self.piano.is_playing and not self.piano.is_paused:
            self.piano.pause_animation()
            self.pause_button.config(text="继续")
    
    def on_progress_release(self, event):
        """进度条释放时"""
        if hasattr(self, 'is_dragging') and self.is_dragging:
            # 跳转到指定位置（毫秒转换为秒）
            current_ms = self.progress_var.get()
            seek_time = current_ms / 1000
            
            # 如果之前正在播放，则继续播放
            if self.piano.is_playing:
                self.piano.start_animation(self.window, seek_time)
            else:
                # 否则直接跳转到指定位置
                self.piano.seek_to_position(seek_time)
                self.current_time_label.config(text=self.format_time_ms(seek_time))
            
            # 更新画布
            self.canvas.draw()
            self.is_dragging = False
    
    def on_closing(self):
        """关闭窗口"""
        if self.piano:
            self.piano.stop_animation()
        self.window.destroy()


# 使用示例
if __name__ == "__main__":
    print("=== MIDI钢琴可视化学习工具 ===")
    print("功能特点:")
    print("  - 左手(通道5)按键显示为绿色")
    print("  - 右手(通道1)按键显示为红色")
    print("  - 时间精度: 1毫秒")
    print("  - 进度条精度: 5毫秒")
    print("\n1. 直接运行PianoKeyboard类创建静态钢琴键盘")
    print("2. 运行MIDIVisualizer类创建带有GUI的可视化工具")
    
    choice = input("请选择模式 (1: 静态键盘, 2: MIDI可视化工具): ")
    
    if choice == "1":
        print("生成88键钢琴键盘（A0到C8）...")
        
        # 创建默认参数的钢琴键盘
        piano = PianoKeyboard(use_tk_gui=False)
        
        # 保存图片到默认位置
        piano.save_image()
        
        # 显示图片
        piano.show()
    
    elif choice == "2":
        print("启动MIDI钢琴可视化学习工具...")
        visualizer = MIDIVisualizer()
        visualizer.create_gui()
    
    else:
        print("无效选择，程序退出。")