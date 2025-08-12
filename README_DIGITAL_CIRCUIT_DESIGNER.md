# Digital Circuit Designer

Một ứng dụng thiết kế và mô phỏng mạch số tương tác với giao diện kéo-thả, hỗ trợ học tập hệ thống số và thiết kế RTL.

## ✨ Tính năng chính

### 🎨 Giao diện thiết kế trực quan
- **Kéo-thả cổng logic**: AND, OR, XOR, NOT, NAND, NOR, XNOR
- **Thành phần tuần tự**: D Flip-Flop, JK Flip-Flop, T Flip-Flop, SR Latch
- **Thành phần I/O**: Input, Output, Clock generator, LED, Switch
- **Grid snapping**: Căn chỉnh tự động theo lưới
- **Zoom và Pan**: Phóng to/thu nhỏ và di chuyển canvas

### ⚡ Mô phỏng thời gian thực
- **Truyền tín hiệu trực quan**: 
  - Tín hiệu HIGH = màu đỏ 🔴
  - Tín hiệu LOW = màu đen ⚫
  - Tín hiệu UNKNOWN = màu xám 🔘
- **Độ trễ lan truyền**: Mô phỏng delay thực tế của cổng logic
- **Clock generator**: Tạo xung clock với tần số điều chỉnh được
- **Interactive inputs**: Click để toggle trạng thái input

### 📊 Công cụ phân tích
- **Timing Diagram**: Biểu đồ thời gian của các tín hiệu
- **Truth Table Generator**: Tự động tạo bảng chân lý
- **Signal History**: Lưu trữ lịch sử thay đổi tín hiệu
- **Circuit Analysis**: Phân tích độ phức tạp mạch

### 🔧 Thiết kế RTL
- **Hierarchical Design**: Thiết kế phân cấp
- **Module Creation**: Tạo module tùy chỉnh
- **Verilog Export**: Xuất code Verilog HDL
- **VHDL Support**: Hỗ trợ xuất VHDL (tương lai)

## 📋 Yêu cầu hệ thống

- Python 3.7+
- tkinter (GUI framework)
- PIL/Pillow (xử lý hình ảnh)
- matplotlib (biểu đồ)
- numpy (tính toán)
- networkx (phân tích đồ thị)

## 🚀 Cài đặt

```bash
# Cài đặt dependencies
pip install -r requirements_digital_circuit.txt

# Chạy ứng dụng
python 31_digital_circuit_designer.py
```

## 📖 Hướng dẫn sử dụng

### Bước 1: Tạo mạch cơ bản

1. **Thêm cổng logic**:
   - Click vào nút cổng trong toolbar (AND, OR, NOT, v.v.)
   - Hoặc kéo từ Component Library bên trái
   - Cổng sẽ xuất hiện tại vị trí con trỏ

2. **Thêm Input/Output**:
   - Thêm INPUT gates cho tín hiệu đầu vào
   - Thêm OUTPUT gates cho tín hiệu đầu ra
   - Click vào INPUT để toggle HIGH/LOW

3. **Kết nối các cổng**:
   - Click vào pin đầu ra (màu đỏ) của cổng nguồn
   - Click vào pin đầu vào (màu xanh) của cổng đích
   - Dây kết nối sẽ được tạo tự động

### Bước 2: Mô phỏng mạch

1. **Bắt đầu simulation**:
   - Click "Start Sim" trong toolbar
   - Hoặc menu Simulation → Start Simulation

2. **Quan sát tín hiệu**:
   - Dây màu đỏ = tín hiệu HIGH (1)
   - Dây màu đen = tín hiệu LOW (0)
   - Dây màu xám = tín hiệu UNKNOWN

3. **Tương tác**:
   - Click vào INPUT gates để thay đổi trạng thái
   - Quan sát sự lan truyền tín hiệu qua mạch

### Bước 3: Phân tích mạch

1. **Timing Diagram**:
   - Menu Simulation → Timing Diagram
   - Xem biểu đồ thời gian của tất cả tín hiệu

2. **Truth Table**:
   - Menu Simulation → Truth Table
   - Chọn input và output pins
   - Tự động tạo bảng chân lý

3. **Export Verilog**:
   - Menu File → Export Verilog
   - Xuất mạch thành code Verilog HDL

## 🎯 Ví dụ mạch cơ bản

### 1. Half Adder (Bộ cộng nửa)
```
Input A ──┐
          ├── XOR ──── Sum
Input B ──┘
    │
    └────── AND ──── Carry
```

**Cách tạo**:
1. Thêm 2 INPUT gates (A, B)
2. Thêm 1 XOR gate và 1 AND gate
3. Thêm 2 OUTPUT gates (Sum, Carry)
4. Kết nối: A,B → XOR → Sum và A,B → AND → Carry

### 2. SR Latch (Chốt SR)
```
S ──── NOR ──┐
       ↑    │
       │    ├── Q
       └────┘
       ┌────┐
       │    ├── Q'
       ↓    │
R ──── NOR ──┘
```

**Cách tạo**:
1. Thêm 2 INPUT gates (S, R)
2. Thêm 2 NOR gates
3. Kết nối chéo để tạo feedback loop
4. Thêm OUTPUT gates cho Q và Q'

### 3. 4-bit Counter
```
Clock ──── D-FF ──── D-FF ──── D-FF ──── D-FF
           │        │        │        │
           Q0       Q1       Q2       Q3
```

## 🔍 Tính năng nâng cao

### Custom Components
```python
# Tạo component tùy chỉnh
class CustomGate(LogicGate):
    def __init__(self, position):
        super().__init__(GateType.CUSTOM, position)
        self.label = "MY_GATE"
    
    def compute_output(self, current_time=0):
        # Logic tùy chỉnh
        return {self.output_pins[0].id: LogicState.HIGH}
```

### Verilog Export
```verilog
module circuit (
    input_A,
    input_B,
    output_Sum,
    output_Carry
);
    input input_A;
    input input_B;
    output output_Sum;
    output output_Carry;
    
    wire wire_A_to_XOR;
    wire wire_B_to_XOR;
    
    xor xor_gate (output_Sum, input_A, input_B);
    and and_gate (output_Carry, input_A, input_B);
endmodule
```

### Timing Analysis
- **Setup Time**: Thời gian setup của flip-flop
- **Hold Time**: Thời gian hold của flip-flop  
- **Propagation Delay**: Độ trễ lan truyền qua cổng
- **Clock Skew**: Độ lệch clock giữa các flip-flop

## ⌨️ Phím tắt

| Phím | Chức năng |
|------|-----------|
| `Ctrl+N` | New Circuit |
| `Ctrl+O` | Open Circuit |
| `Ctrl+S` | Save Circuit |
| `Ctrl+Z` | Undo |
| `Ctrl+Y` | Redo |
| `Space` | Start/Stop Simulation |
| `R` | Reset Simulation |
| `G` | Toggle Grid |
| `+` | Zoom In |
| `-` | Zoom Out |
| `0` | Reset Zoom |
| `Del` | Delete Selected |

## 🎨 Customization

### Themes
```python
# Dark Theme
colors = {
    'background': '#2B2B2B',
    'gate_fill': '#404040',
    'wire_high': '#FF4444',
    'wire_low': '#FFFFFF',
    'grid': '#505050'
}
```

### Gate Symbols
- **IEEE Standard**: Ký hiệu chuẩn IEEE
- **DIN Standard**: Ký hiệu chuẩn DIN (Đức)
- **Custom Symbols**: Tự định nghĩa ký hiệu

## 🔧 Troubleshooting

### Vấn đề thường gặp

1. **Mạch không hoạt động**:
   - Kiểm tra tất cả connections
   - Đảm bảo có INPUT và OUTPUT gates
   - Verify logic gate connections

2. **Simulation chậm**:
   - Giảm số lượng gates
   - Tăng simulation step time
   - Disable timing diagram recording

3. **Export Verilog lỗi**:
   - Kiểm tra tên gates hợp lệ
   - Đảm bảo không có loops
   - Verify input/output connections

## 📚 Tài liệu học tập

### Digital Logic Fundamentals
1. **Boolean Algebra**: Đại số Boolean
2. **Logic Gates**: Các cổng logic cơ bản
3. **Sequential Circuits**: Mạch tuần tự
4. **Combinational Circuits**: Mạch tổ hợp

### Advanced Topics
1. **State Machines**: Máy trạng thái
2. **Memory Design**: Thiết kế bộ nhớ
3. **CPU Architecture**: Kiến trúc CPU
4. **FPGA Programming**: Lập trình FPGA

## 🌟 Ví dụ dự án

### 1. Simple CPU
- **ALU**: Arithmetic Logic Unit
- **Control Unit**: Đơn vị điều khiển
- **Registers**: Thanh ghi
- **Memory Interface**: Giao tiếp bộ nhớ

### 2. Digital Clock
- **Counter Chains**: Chuỗi bộ đếm
- **7-Segment Display**: Hiển thị 7 đoạn
- **Time Setting**: Thiết lập thời gian

### 3. Traffic Light Controller
- **State Machine**: Máy trạng thái
- **Timer Logic**: Logic đếm thời gian
- **Sensor Interface**: Giao tiếp cảm biến

## 🤝 Đóng góp

Chúng tôi hoan nghênh mọi đóng góp:

1. **Bug Reports**: Báo cáo lỗi
2. **Feature Requests**: Đề xuất tính năng
3. **Code Contributions**: Đóng góp code
4. **Documentation**: Cải thiện tài liệu

## 📄 License

Dự án này được phát hành dưới giấy phép MIT License.

## 🔮 Roadmap

### Version 2.0
- [ ] VHDL Export support
- [ ] Waveform viewer improvements
- [ ] Component library expansion
- [ ] Performance optimizations

### Version 3.0
- [ ] FPGA synthesis support
- [ ] Advanced timing analysis
- [ ] Collaborative editing
- [ ] Cloud simulation

---

**Happy Circuit Designing! 🚀**

Tạo ra những mạch số tuyệt vời và khám phá thế giới hệ thống số! 