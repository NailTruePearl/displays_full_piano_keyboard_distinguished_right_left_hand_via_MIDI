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
from tkinter import filedialog
import threading
import queue
import warnings
import pygame
import pygame.midi
import os

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
        self.active_color = 'red'  # 激活键的颜色
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
        self.playback_speed = 1.0
        
        # 动画相关
        self.animation = None
        self.animation_thread = None
        self.stop_animation_flag = False
        
        # 设置保存路径
        self.save_path = r"D:xxxxxxxxxxxxxx.png"
        
        # 事件队列，用于线程间通信
        self.event_queue = queue.Queue()
        
        self.setup_keyboard()
        
        if not self.use_tk_gui:
            # 连接关闭事件
            self.fig.canvas.mpl_connect('close_event', self.on_close)

         # 音频播放相关
        self.audio_initialized = False
        # 音频播放相关
        self.midi_out = None
        self.midi_playing = False  # 新增标志
        self.init_audio()
        
        # MIDI音频播放器
        self.midi_player = None
        self.midi_file_path = None
    
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
                        y_offset = 3.5 * self.staff_line_spacing + note_index * (self.staff_line_spacing / 2)
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
            active_notes = {}  # 存储正在播放的音符，键为音高，值为开始时间
            
            # 解析所有轨道
            for i, track in enumerate(midi_file.tracks):
                print(f"\n轨道 {i}: {track.name}")
                
                track_time = 0
                for msg in track:
                    track_time += msg.time
                    
                    if msg.type == 'note_on' and msg.velocity > 0:
                        # 音符开始
                        active_notes[msg.note] = track_time
                    elif msg.type == 'note_off' or (msg.type == 'note_on' and msg.velocity == 0):
                        # 音符结束
                        if msg.note in active_notes:
                            start_time = active_notes[msg.note]
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
                                    'velocity': msg.velocity if hasattr(msg, 'velocity') else 64
                                })
                            
                            # 从活跃音符中移除
                            del active_notes[msg.note]
            
            # 按开始时间排序
            self.midi_notes.sort(key=lambda x: x['start'])
            
            # 计算总时长
            if self.midi_notes:
                total_duration = max(note['end'] for note in self.midi_notes)
                print(f"\n解析完成！共找到 {len(self.midi_notes)} 个音符事件")
                print(f"总时长: {total_duration:.2f} 拍")
                
                # 统计音符频率
                note_count = {}
                for note in self.midi_notes:
                    if note['note'] in note_count:
                        note_count[note['note']] += 1
                    else:
                        note_count[note['note']] = 1
                
                print("\n最常见的10个音符:")
                sorted_notes = sorted(note_count.items(), key=lambda x: x[1], reverse=True)
                for note, count in sorted_notes[:10]:
                    print(f"  {note}: {count}次")
            
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
    
    def activate_key(self, note_name):
        """
        激活指定的键（变为红色）
        
        参数:
        note_name: 音符名称，如 "C4", "A#5"
        """
        # 激活琴键
        if note_name in self.key_dict:
            rect = self.key_dict[note_name]
            rect.set_facecolor(self.active_color)
            rect.set_edgecolor(self.active_color)
        
        # 激活五线谱上的音符（如果存在）
        if note_name in self.staff_note_dict:
            note_data = self.staff_note_dict[note_name]
            note_data['note_head'].set_facecolor(self.active_color)
            note_data['note_head'].set_edgecolor(self.active_color)
            
            if note_data['stem']:
                note_data['stem'].set_color(self.active_color)
    
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
    
    def update_animation(self):
        """
        更新动画帧
        """
        if not self.midi_notes:
            return
        
        # 重置所有键的颜色
        self.reset_all_keys()
        
        # 计算当前时间
        current_time = (time.time() - self.animation_start_time) * self.playback_speed
        
        # 激活当前时间正在弹奏的键
        active_notes = []
        for note in self.midi_notes:
            # 如果音符在当前时间范围内
            if note['start'] <= current_time <= note['end']:
                self.activate_key(note['note'])
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
        total_duration = max(note['end'] for note in self.midi_notes)
        if current_time > total_duration:
            return False
        
        return True
    
    def animation_loop(self):
        """动画循环"""
        interval = 50  # 毫秒
        
        while not self.stop_animation_flag:
            if not self.update_animation():
                break
            
            # 等待下一帧
            time.sleep(interval / 1000.0)
        
        # 动画结束，重置标志
        self.stop_animation_flag = False
    
    def start_animation(self, tk_window=None):
        """开始播放动画"""
        if not self.midi_notes:
            print("没有加载MIDI文件，请先加载MIDI文件")
            return
        
        # 停止之前的动画和音频
        self.stop_animation()
        
        # 重置所有键
        self.reset_all_keys()
        
        # 计算动画总时长（以秒为单位）
        total_duration = max(note['end'] for note in self.midi_notes)
        
        print(f"开始播放动画，总时长: {total_duration:.2f}秒")
        print(f"播放速度: {self.playback_speed}x")
        
        # 设置动画开始时间
        self.animation_start_time = time.time()
        
        # 重置停止标志
        self.stop_animation_flag = False
        
        # 开始播放音频
        audio_started = self.play_midi_audio()
        if not audio_started:
            print("警告：音频播放失败，继续显示键位动画")
        

        if self.use_tk_gui:
            # 在Tkinter中，我们需要通过Tkinter主窗口的after方法来调度
            # 保存对Tkinter窗口的引用
            self.tk_window = tk_window
            
            def tk_animation_update():
                if not self.stop_animation_flag:
                    if self.update_animation():
                        # 继续下一次更新
                        self.tk_window.after(50, tk_animation_update)
            
            # 启动动画
            self.tk_window.after(0, tk_animation_update)
        else:
            # 在独立窗口中，使用线程运行动画
            self.animation_thread = threading.Thread(target=self.animation_loop, daemon=True)
            self.animation_thread.start()
            
            # 显示窗口（非阻塞）
            if not plt.fignum_exists(self.fig.number):
                plt.show(block=False)
    
    def stop_animation(self):
        """停止播放动画"""
        self.stop_animation_flag = True
        # 停止音频播放
        self.stop_midi_audio()
        
        if self.animation_thread and self.animation_thread.is_alive():
            self.animation_thread.join(timeout=1.0)
    
    def on_close(self, event):
        """处理窗口关闭事件"""
        self.stop_animation()
        self.cleanup()  # 添加这行
    
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
    
    def init_audio(self):
        """初始化音频系统"""
        try:
            # 先初始化pygame
            if not pygame.get_init():
                pygame.init()
            
            # 初始化音频mixer（用于播放普通音频）
            if not pygame.mixer.get_init():
                pygame.mixer.init(frequency=44100, size=-16, channels=2, buffer=4096)
            
            # 初始化midi系统
            pygame.midi.init()
            
            # 获取可用的midi输出设备
            midi_outputs = []
            device_info_list = []
            
            for i in range(pygame.midi.get_count()):
                device_info = pygame.midi.get_device_info(i)
                interface = device_info[0].decode() if device_info[0] else "Unknown"
                name = device_info[1].decode() if device_info[1] else "Unknown"
                is_input = device_info[2]
                is_output = device_info[3]
                
                print(f"设备 {i}: 接口={interface}, 名称={name}, "
                    f"输入={is_input}, 输出={is_output}")
                
                # 检查是否为输出设备
                if is_output:
                    midi_outputs.append(i)
                    device_info_list.append((i, interface, name))
                    print(f"找到MIDI输出设备 {i}: {name}")
            
            self.midi_out = None
            
            # 优先尝试软件合成器
            preferred_devices = ["Microsoft GS Wavetable Synth", "Microsoft MIDI Mapper"]
            
            for device_id, interface, name in device_info_list:
                for preferred in preferred_devices:
                    if preferred in name:
                        try:
                            print(f"尝试打开首选设备: {name} (ID: {device_id})")
                            self.midi_out = pygame.midi.Output(device_id, 0)
                            print(f"成功打开MIDI输出设备: {device_id} - {name}")
                            self.audio_initialized = True
                            return
                        except Exception as e:
                            print(f"无法打开首选设备 {device_id}: {e}")
            
            # 如果首选设备都失败，尝试其他输出设备
            for device_id, interface, name in device_info_list:
                if device_id not in [d[0] for d in device_info_list if any(p in d[2] for p in preferred_devices)]:
                    try:
                        print(f"尝试打开备用设备: {name} (ID: {device_id})")
                        self.midi_out = pygame.midi.Output(device_id, 0)
                        print(f"成功打开MIDI输出设备: {device_id} - {name}")
                        self.audio_initialized = True
                        return
                    except Exception as e:
                        print(f"无法打开备用设备 {device_id}: {e}")
            
            # 如果所有设备都失败，只记录警告但继续运行
            if self.midi_out is None:
                print("警告：无法打开任何MIDI输出设备，将使用软件合成")
                self.audio_initialized = True  # 仍然标记为已初始化，使用软件合成
            
        except Exception as e:
            print(f"音频初始化失败: {e}")
            self.audio_initialized = True  # 即使失败也标记为True，允许使用软件合成
            self.midi_out = None
    
    def load_midi_audio(self, filepath):
        """加载MIDI音频文件（这个方法在pygame中主要用于预加载，实际MIDI播放需要另外处理）"""
        if not self.audio_initialized:
            print("音频系统未初始化，无法加载音频")
            return False
        
        try:
            # 保存文件路径用于后续播放
            self.midi_file_path = filepath
            
            # 这里只是保存文件路径，实际的MIDI播放将由专门的MIDI播放器处理
            print(f"MIDI文件路径已设置: {filepath}")
            
            # 测试播放一个音符以确保MIDI输出工作正常
            if self.midi_out:
                self.midi_out.note_on(60, 64)  # 播放C4音符
                time.sleep(0.1)
                self.midi_out.note_off(60, 64)
                print("MIDI输出测试成功")
            
            return True
        except Exception as e:
            print(f"设置MIDI文件路径失败: {e}")
            return False
    
    def play_midi_audio(self):
        """播放MIDI音频"""
        if not self.audio_initialized:
            print("音频系统未初始化，无法播放音频")
            return False
        
        try:
            # 如果MIDI输出设备不可用，尝试使用pygame的mixer播放MIDI
            if not self.midi_out:
                print("无MIDI硬件输出设备，尝试使用软件合成...")
                return self._play_midi_with_mixer()
            
            # 使用独立的线程播放MIDI文件
            threading.Thread(target=self._play_midi_thread, daemon=True).start()
            return True
        except Exception as e:
            print(f"播放音频失败: {e}")
            return False
    
    def _play_midi_with_mixer(self):
        """使用pygame mixer播放MIDI（软件合成）"""
        try:
            if not hasattr(self, 'midi_file_path') or not self.midi_file_path:
                print("没有MIDI文件路径")
                return False
            
            pygame.mixer.music.load(self.midi_file_path)
            pygame.mixer.music.play()
            print("使用软件合成播放MIDI音频")
            return True
        except Exception as e:
            print(f"软件合成播放失败: {e}")
            return False
    
    def _play_midi_thread(self):
        """在独立线程中播放MIDI"""
        if not self.midi_notes:
            print("没有MIDI音符数据可播放")
            return
        
        try:
            print("开始播放MIDI音频...")
            
            # 记录开始时间
            start_time = time.time()
            
            # 播放所有音符
            for note_event in self.midi_notes:
                # 检查是否需要停止
                if self.stop_animation_flag:
                    break
                    
                # 计算延迟时间
                current_elapsed = time.time() - start_time
                note_start_time = note_event['start'] / self.playback_speed
                
                if current_elapsed < note_start_time:
                    sleep_time = note_start_time - current_elapsed
                    if sleep_time > 0:
                        time.sleep(sleep_time)
                
                # 播放音符
                try:
                    # 如果midi_out可用，使用硬件播放
                    if self.midi_out and self.audio_initialized:
                        velocity = min(127, max(0, note_event['velocity']))
                        self.midi_out.note_on(note_event['midi_note'], velocity)
                        
                        # 计算音符时长
                        duration = note_event['duration'] / self.playback_speed
                        
                        # 在另一个线程中处理音符关闭
                        def note_off(midi_note, delay, midi_out):
                            time.sleep(delay)
                            if midi_out:
                                try:
                                    midi_out.note_off(midi_note, 0)
                                except:
                                    pass
                        
                        threading.Thread(
                            target=note_off, 
                            args=(note_event['midi_note'], duration, self.midi_out),
                            daemon=True
                        ).start()
                    else:
                        # 使用软件合成（通过播放完整的MIDI文件）
                        if not hasattr(self, 'midi_playing') or not self.midi_playing:
                            self._play_midi_with_mixer()
                            self.midi_playing = True
                            
                except Exception as e:
                    print(f"播放音符失败: {e}")
                    # 尝试使用软件合成
                    if not hasattr(self, 'midi_playing') or not self.midi_playing:
                        self._play_midi_with_mixer()
                        self.midi_playing = True
            
            print("MIDI音频播放完成")
        except Exception as e:
            print(f"MIDI播放线程出错: {e}")
    
    def stop_midi_audio(self):
        """停止播放MIDI音频"""
        # 设置停止标志
        self.stop_animation_flag = True
        
        # 停止软件合成
        try:
            if pygame.mixer.get_init():
                pygame.mixer.music.stop()
        except:
            pass
        
        # 关闭硬件MIDI音符
        try:
            if hasattr(self, 'midi_out') and self.midi_out:
                self.midi_out.note_off(0, 0)  # 发送所有音符关闭
        except:
            pass
        
        # 重置播放状态
        self.midi_playing = False
    
    def pause_midi_audio(self):
        """暂停播放MIDI音频"""
        if not self.audio_initialized:
            return
        
        try:
            pygame.mixer.music.pause()
        except:
            pass
    
    def unpause_midi_audio(self):
        """继续播放MIDI音频"""
        if not self.audio_initialized:
            return
        
        try:
            pygame.mixer.music.unpause()
        except:
            pass
    
    def cleanup(self):
        """清理资源"""
        print("清理音频资源...")
        
        # 设置停止标志
        self.stop_animation_flag = True
        
        # 等待一小段时间让线程有机会停止
        time.sleep(0.1)
        
        # 停止软件合成音频
        try:
            if pygame.mixer.get_init():
                pygame.mixer.music.stop()
        except:
            pass
        
        # 关闭MIDI输出设备
        try:
            if hasattr(self, 'midi_out') and self.midi_out:
                try:
                    # 发送所有音符关闭消息
                    self.midi_out.note_off(0, 0)
                    time.sleep(0.05)
                    self.midi_out.close()
                    print("MIDI输出已关闭")
                except Exception as e:
                    print(f"关闭MIDI输出时出错: {e}")
        except:
            pass
        
        # 清理pygame资源
        try:
            # 清理mixer
            if pygame.mixer.get_init():
                pygame.mixer.quit()
            
            # 清理midi
            if pygame.midi.get_init():
                pygame.midi.quit()
                
            # 注意：不调用pygame.quit()，因为可能影响GUI中的其他pygame组件
        except Exception as e:
            print(f"清理音频资源时出错: {e}")
    
    def __del__(self):
        """析构函数，确保资源被清理"""
        self.cleanup()

    def set_midi_file(self, filepath):
        """直接设置MIDI文件路径"""
        if not os.path.exists(filepath):
            print(f"文件不存在: {filepath}")
            return False
        
        # 加载MIDI数据
        success = self.load_midi_file(filepath)
        if success:
            # 设置音频文件路径
            self.midi_file_path = filepath
            return True
        return False    



class MIDIVisualizer:
    """MIDI可视化器，提供GUI界面"""
    
    def __init__(self, default_midi_path=None):
        self.piano = None
        self.window = None
        self.canvas = None
        self.animation_id = None
        self.audio_button = None
        self.audio_enabled = True  # 默认启用音频
        
        # 如果提供了默认路径，使用它；否则使用硬编码的默认路径
        if default_midi_path:
            self.default_midi_path = default_midi_path
        else:
            self.default_midi_path = r"D:\曲谱\want_to_see_you30.mid"  # 存储默认MIDI文件路径
        
    def create_gui(self):
        """创建GUI界面"""
        # 创建主窗口
        self.window = tk.Tk()
        self.window.title("MIDI钢琴可视化学习工具")
        self.window.geometry("1000x800")
        
        # 设置窗口关闭事件
        self.window.protocol("WM_DELETE_WINDOW", self.on_closing)
        
        # 创建框架
        top_frame = tk.Frame(self.window)
        top_frame.pack(side="top", fill="x", padx=10, pady=5)
        
        # 标题
        title_label = tk.Label(top_frame, text="MIDI钢琴可视化学习工具", 
                              font=("Arial", 16, "bold"))
        title_label.pack(pady=10)
        
        # 控制按钮框架
        control_frame = tk.Frame(top_frame)
        control_frame.pack(pady=10)
        
        self.audio_button = tk.Button(control_frame, text="关闭音频", 
                                     command=self.toggle_audio,
                                     font=("Arial", 12), bg="#9C27B0", fg="white",
                                     height=2, width=15)
        self.audio_button.pack(side="left", padx=5)

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
        
        self.stop_button = tk.Button(control_frame, text="停止播放", 
                                    command=self.stop_playback,
                                    font=("Arial", 12), bg="#f44336", fg="white",
                                    height=2, width=15, state="disabled")
        self.stop_button.pack(side="left", padx=5)
        
        self.reset_button = tk.Button(control_frame, text="重置视图", 
                                     command=self.reset_view,
                                     font=("Arial", 12), bg="#FF9800", fg="white",
                                     height=2, width=15)
        self.reset_button.pack(side="left", padx=5)
        
        # 播放速度控制
        speed_frame = tk.Frame(top_frame)
        speed_frame.pack(pady=10)
        
        speed_label = tk.Label(speed_frame, text="播放速度:", font=("Arial", 12))
        speed_label.pack(side="left", padx=5)
        
        self.speed_var = tk.DoubleVar(value=1.0)
        speed_scale = tk.Scale(speed_frame, from_=0.5, to=2.0, 
                              resolution=0.1, orient="horizontal",
                              variable=self.speed_var, length=200,
                              command=self.update_speed)
        speed_scale.pack(side="left", padx=5)
        
        # 状态显示
        self.status_label = tk.Label(top_frame, text="等待加载MIDI文件...", 
                                    font=("Arial", 10), fg="blue")
        self.status_label.pack(pady=10)
        
        # 初始化钢琴键盘
        from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
        self.piano = PianoKeyboard(use_tk_gui=True)
        
        # 如果有默认的MIDI文件路径，自动加载
        if self.default_midi_path and os.path.exists(self.default_midi_path):
            # 延迟加载，确保GUI完全创建后再加载MIDI
            self.window.after(100, lambda: self.load_default_midi_file(self.default_midi_path))
        
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
        
        # 运行GUI
        self.window.mainloop()
    
    def toggle_audio(self):
        """切换音频开关"""
        self.audio_enabled = not self.audio_enabled
        
        if self.audio_enabled:
            self.audio_button.config(text="关闭音频", bg="#9C27B0")
            self.status_label.config(text="音频已启用", fg="purple")
        else:
            self.audio_button.config(text="启用音频", bg="#673AB7")
            self.status_label.config(text="音频已禁用", fg="purple")
    
    def start_playback(self):
        """开始播放"""
        if self.piano and self.piano.midi_notes:
            # 设置音频开关
            if not self.audio_enabled:
                # 如果音频被禁用，停止当前可能正在播放的音频
                self.piano.stop_midi_audio()
            
            self.status_label.config(text="正在播放...", fg="green")
            self.play_button.config(state="disabled")
            self.stop_button.config(state="normal")
            self.window.update()
            
            # 设置播放速度
            self.piano.playback_speed = self.speed_var.get()
            
            # 开始动画，传入Tkinter主窗口
            self.piano.start_animation(self.window)
    
    
    def load_midi_file(self):
        """加载MIDI文件"""
        # 打开文件选择对话框
        filepath = filedialog.askopenfilename(
            title="选择MIDI文件",
            filetypes=[("MIDI文件", "*.mid;*.midi"), ("所有文件", "*.*")]
        )
        
        if filepath:
            print(f"选择的MIDI文件: {filepath}")
            self.status_label.config(text=f"正在加载: {os.path.basename(filepath)}...", fg="blue")
            self.window.update()
            
            # 加载MIDI文件
            success = self.piano.set_midi_file(filepath)
            if success:
                self.status_label.config(text=f"已加载: {os.path.basename(filepath)}", fg="green")
                self.play_button.config(state="normal")
                self.stop_button.config(state="disabled")
                
                # 重新绘制画布
                if hasattr(self, 'canvas') and self.canvas:
                    self.canvas.draw()
                
                print("MIDI文件加载成功")
            else:
                self.status_label.config(text="加载MIDI文件失败", fg="red")
                print("加载MIDI文件失败")
    
    def start_playback(self):
        """开始播放"""
        if self.piano and self.piano.midi_notes:
            self.status_label.config(text="正在播放...", fg="green")
            self.play_button.config(state="disabled")
            self.stop_button.config(state="normal")
            self.window.update()
            
            # 设置播放速度
            self.piano.playback_speed = self.speed_var.get()
            
            # 开始动画，传入Tkinter主窗口
            self.piano.start_animation(self.window)
    
    def stop_playback(self):
        """停止播放"""
        if self.piano:
            self.piano.stop_animation()
            self.status_label.config(text="播放已停止", fg="orange")
            self.play_button.config(state="normal")
            self.stop_button.config(state="disabled")
    
    def reset_view(self):
        """重置视图"""
        if self.piano:
            self.piano.reset_all_keys()
            self.canvas.draw()
            self.status_label.config(text="视图已重置", fg="blue")
    
    def update_speed(self, value):
        """更新播放速度"""
        if self.piano:
            self.piano.playback_speed = float(value)
            self.status_label.config(text=f"播放速度: {value}x", fg="purple")
    
    def on_closing(self):
        """关闭窗口"""
        if self.piano:
            self.piano.cleanup()  # 修改为调用cleanup方法
        self.window.destroy()
    
    def load_default_midi_file(self, filepath):
        """加载默认的MIDI文件"""
        if self.piano and filepath:
            success = self.piano.set_midi_file(filepath)
            if success:
                self.status_label.config(text=f"已加载: {os.path.basename(filepath)}", fg="green")
                self.play_button.config(state="normal")
                self.stop_button.config(state="disabled")
                
                # 重新绘制画布
                if hasattr(self, 'canvas') and self.canvas:
                    self.canvas.draw()
                print("默认MIDI文件加载成功")
            else:
                self.status_label.config(text="加载默认MIDI文件失败", fg="red")



# 使用示例
if __name__ == "__main__":
    print("=== MIDI钢琴可视化学习工具 ===")
    print("1. 直接运行PianoKeyboard类创建静态钢琴键盘")
    print("2. 运行MIDIVisualizer类创建带有GUI的可视化工具")
    
    # 在这里直接指定你的MIDI文件路径
    DEFAULT_MIDI_PATH = r"D:\xxxxxxxxxxxxxxxxxxx.mid" # 修改为你的MIDI文件路径
    
    choice = input("请选择模式 (1: 静态键盘, 2: MIDI可视化工具): ")
    
    if choice == "1":
        print("生成88键钢琴键盘（A0到C8）...")
        
        # 创建默认参数的钢琴键盘
        piano = PianoKeyboard(use_tk_gui=False)
        
        # 可选：直接加载指定的MIDI文件
        if os.path.exists(DEFAULT_MIDI_PATH):
            load_midi = input(f"是否加载MIDI文件 {DEFAULT_MIDI_PATH}? (y/n): ")
            if load_midi.lower() == 'y':
                if piano.set_midi_file(DEFAULT_MIDI_PATH):
                    print("MIDI文件加载成功，按任意键开始动画演示...")
                    input()
                    piano.start_animation()
        
        try:
            # 保存图片到默认位置
            piano.save_image()
            
            # 显示图片
            piano.show()
        finally:
            # 确保资源被清理
            piano.cleanup()
    
    elif choice == "2":
        print("启动MIDI钢琴可视化学习工具...")
        
        # 检查默认MIDI文件是否存在
        if os.path.exists(DEFAULT_MIDI_PATH):
            print(f"发现默认MIDI文件: {DEFAULT_MIDI_PATH}")
            use_default = input("是否使用此文件? (y/n): ")
            if use_default.lower() == 'y':
                visualizer = MIDIVisualizer(default_midi_path=DEFAULT_MIDI_PATH)
            else:
                visualizer = MIDIVisualizer()
        else:
            print(f"默认MIDI文件不存在: {DEFAULT_MIDI_PATH}")
            visualizer = MIDIVisualizer()
            
        try:
            visualizer.create_gui()
        except Exception as e:
            print(f"程序运行出错: {e}")
        finally:
            # 如果GUI没有正常清理，确保资源被释放
            if hasattr(visualizer, 'piano') and visualizer.piano:
                visualizer.piano.cleanup()
    
    else:
        print("无效选择，程序退出。")