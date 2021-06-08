// Your code
module CHIP(
    clk,
    rst_n,
    // For mem_D
    mem_wen_D,
    mem_addr_D,
    mem_wdata_D,
    mem_rdata_D,
    // For mem_I
    mem_addr_I,
    mem_rdata_I);

    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;
    output [31:0] mem_addr_D ;
    output [31:0] mem_wdata_D;
    input  [31:0] mem_rdata_D;
    // For mem_I
    output [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;
    
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    /*wire   [31:0] PC_nxt      ;*/          //
    reg    [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    wire   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg
    reg   [1:0]state, state_nxt;
    reg   [2:0]  type, type_nxt; // if necessary ?(maybe not nxt)
    reg   [2:0]  func, func_nxt; 
    reg   [31:0] imm           ;
    reg   [31:0] alu_out       ;
    reg   [31:0] alu_out_nxt   ;
    reg   check_branch         ;
    reg   [31:0] write_rd      ;
    reg   [31:0] write_rd_nxt  ;
    reg   write, write_nxt     ;
    reg   ctrl, ctrl_nxt       ; // for mem_wen_D
    reg   [14:0] addr_I        ;
    reg   [14:0] addr_I_nxt    ;
    wire  valid                ; // for mul_valid
    wire  ready                ; // for mul_ready
    wire  [63:0] out           ; // for mul_out


    // Definition of state
    parameter ID = 2'b00;
    parameter EX = 2'b01;
    parameter MW = 2'b10;  // MEM & WB

    // Definition of type
    // R:0, I:1, S:2, B:3, U:4, J:5
    parameter R = 3'b000;
    parameter I = 3'b001;
    parameter S = 3'b010;
    parameter B = 3'b011;
    parameter U = 3'b100;
    parameter J = 3'b101;
    // func may also parameterized ?

    //--------------------------------------------//
    //--R------I------S------B------U------J------//
    //0:ADD    JALR   SW     BEQ    LUI    JAL
    //1:SUB    LW            BNE    AUIPC
    //2:MUL    ADDI          BLT
    //3:       SLTI          BGE
    //4:       SLLI
    //5:       SRLI
    //6:
    //7:
    //--------------------------------------------//

    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//
    
    //---------------------------------------//
    mulDiv mul0(
        .clk(clk),
        .rst_n(rst_n),
        .valid(valid),
        .ready(ready),
        .mode(1'b0),
        .in_A(rs1_data),
        .in_B(rs2_data),
        .out(out));
    //---------------------------------------//
    // Todo: any combinational/sequential circuit
    // Wire assignments
    // output
    assign  mem_wen_D  = ctrl;
    assign  mem_addr_D = alu_out;
    assign  mem_wdata_D = rs2_data;
    assign  mem_addr_I = PC;
    // input internal wires for reg0
    // assign 這邊的條件語法好像有錯，在幫我改一下 謝謝！
    assign  regWrite = write;  // Load
    assign  rs1 = addr_I[9:5];
    assign  rs2 = addr_I[14:10];
    assign  rd  = addr_I[4:0];
    assign  rd_data = (write && rd != 0) ? write_rd : 0;
    assign  valid = (type == R && func == 3'b010 && state == EX) ? 1'b1 : 1'b0; 

    //-------------------------------------------------//
    // 3 cycles for states
    always @(*) begin
        case(state)
            ID : begin
                state_nxt = EX;
            end
            EX : begin
                state_nxt = ((type == I && func == 3'b001)||(type == S && func == 3'b000)) ? MW : ((type == R && func == 3'b010 && !ready) ? EX : ID);
            end
            MW : begin
                state_nxt = ID;
            end
            default : state_nxt = ID;
        endcase
    end

    always @(*) begin  // imm
        case(state)
            EX: begin
                case(type)
                    R:begin
                        imm[31:0] = {32{1'b0}};
                    end
                    I:begin
                        imm[11:0]  = mem_rdata_I[31:20];
                        imm[31:12] = {20{imm[11]}};
                    end
                    S:begin
                        imm[11:5]  = mem_rdata_I[31:25];
                        imm[4:0]   = mem_rdata_I[11:7];
                        imm[31:12] = {20{imm[11]}};
                    end
                    B:begin
                        imm[12] = mem_rdata_I[31];
                        imm[11] = mem_rdata_I[7];
                        imm[10:5]  = mem_rdata_I[30:25];
                        imm[4:1]   = mem_rdata_I[11:8];
                        imm[0]  = 1'b0;
                        imm[31:13] = {19{imm[12]}};
                    end
                    U:begin
                        imm[31:12] = mem_rdata_I[31:12];
                        imm[11:0]  = {12{1'b0}};
                    end
                    J:begin
                        imm[20] = mem_rdata_I[31];
                        imm[19:12] =  mem_rdata_I[19:12];
                        imm[11] = mem_rdata_I[20];
                        imm[10:1]  = mem_rdata_I[30:21];
                        imm[0]  = 1'b0;
                        imm[31:21] = {11{imm[20]}};
                    end
                    default : imm = 0;
                endcase
            end
            default : imm = 0; 
        endcase
    end

    always @(*) begin // Instruction Decode
        case(state)
            ID:begin
                case(mem_rdata_I[6:0])
                    7'b0110111:begin
                        type_nxt = U;   // U-type
                        addr_I_nxt[4:0] = mem_rdata_I[11:7];
                        addr_I_nxt[9:5] = 5'b0;
                        addr_I_nxt[14:10] = 5'b0;
                        //write_nxt = 1;
                        func_nxt = 3'b000;   // LUI
                    end
                    7'b0010111:begin
                        type_nxt = U;   // U-type
                        addr_I_nxt[4:0] = mem_rdata_I[11:7];
                        addr_I_nxt[9:5] = 5'b0;
                        addr_I_nxt[14:10] = 5'b0;
                        //write_nxt = 1;
                        func_nxt = 3'b001;   // AUIPC
                    end
                    7'b1101111:begin
                        type_nxt = J;   // J-type
                        addr_I_nxt[4:0] = mem_rdata_I[11:7];
                        addr_I_nxt[9:5] = 5'b0;
                        addr_I_nxt[14:10] = 5'b0;
                        //write_nxt = 1;
                        func_nxt = 3'b000;   // JAL
                    end
                    7'b1100111:begin
                        type_nxt = I;   // I-type
                        addr_I_nxt[4:0] = mem_rdata_I[11:7];
                        addr_I_nxt[9:5] = mem_rdata_I[19:15];
                        addr_I_nxt[14:10] = 5'b0;
                        //write_nxt = 1;
                        func_nxt = 3'b000;   // JALR
                    end
                    7'b1100011:begin
                        type_nxt = B;   // B-type
                        addr_I_nxt[4:0] = 5'b0;
                        addr_I_nxt[9:5] = mem_rdata_I[19:15];
                        addr_I_nxt[14:10] = mem_rdata_I[24:20];
                        //write_nxt = 0;
                        case(mem_rdata_I[14:12])
                            3'b000:begin
                                func_nxt = 3'b000;   // BEQ
                            end
                            3'b001:begin
                                func_nxt = 3'b001;   // BNE
                            end
                            3'b100:begin
                                func_nxt = 3'b010;   // BLT
                            end
                            3'b101:begin
                                func_nxt = 3'b011;   // BGE
                            end
                        default : func_nxt = func;
                        endcase
                    end
                    7'b0000011:begin
                        type_nxt = I;   // I-type
                        addr_I_nxt[4:0] = mem_rdata_I[11:7];
                        addr_I_nxt[9:5] = mem_rdata_I[19:15];
                        addr_I_nxt[14:10] = 5'b0;
                        //write_nxt = 1;
                        func_nxt = 3'b001;   // LW
                    end
                    7'b0100011:begin
                        type_nxt = S;   // S-type
                        addr_I_nxt[4:0] = 5'b0;
                        addr_I_nxt[9:5] = mem_rdata_I[19:15];
                        addr_I_nxt[14:10] = mem_rdata_I[24:20];
                        //write_nxt = 0;
                        func_nxt = 3'b000;   // SW
                    end
                    7'b0010011:begin
                        type_nxt = I;   // I-type
                        addr_I_nxt[4:0] = mem_rdata_I[11:7];
                        addr_I_nxt[9:5] = mem_rdata_I[19:15];
                        addr_I_nxt[14:10] = 5'b0;
                        //write_nxt = 1;
                        case(mem_rdata_I[14:12])
                            3'b000:begin
                                func_nxt = 3'b010;   // ADDI
                            end
                            3'b010:begin
                                func_nxt = 3'b011;   // SLTI
                            end
                            3'b001:begin
                                func_nxt = 3'b100;   // SLLI
                            end
                            3'b101:begin
                                func_nxt = 3'b101;   // SRLI
                            end
                            default : func_nxt = func;
                        endcase
                    end
                    7'b0110011:begin
                        type_nxt = R;   // R-type
                        addr_I_nxt[4:0] = mem_rdata_I[11:7];
                        addr_I_nxt[9:5] = mem_rdata_I[19:15];
                        addr_I_nxt[14:10] = mem_rdata_I[24:20];
                        case(mem_rdata_I[31:25])
                            7'b0000000:begin
                                func_nxt = 3'b000;   // ADD
                                //write_nxt = 1;
                            end
                            7'b0100000:begin
                                func_nxt = 3'b001;   // SUB
                                //write_nxt = 1;
                            end
                            7'b0000001:begin
                                func_nxt = 3'b010;   // MUL
                                //write_nxt = ready;
                            end
                            default:begin
                                func_nxt = func;
                                //write_nxt = write;
                            end
                        endcase
                    end
                    default: begin
                        type_nxt = type;
                        func_nxt = func;
                        addr_I_nxt = addr_I;
                        //write_nxt = write;
                    end
                endcase
            end
            default: begin
                type_nxt = type;
                func_nxt = func;
                addr_I_nxt = addr_I;
                //write_nxt = write;
            end
        endcase
    end

    //---------------------------------------------------//
    // Subsequent Actions after Instrunction Decode ?
    // OK!!
    //-------------------------------------------------//
    
    always @(*) begin  // EX
        case(state)
            EX: begin
                case(type)
                    R:begin        //R-type
                        case(func)
                            3'b000:begin    //ADD
                                alu_out_nxt = 0;
                                write_rd_nxt = rs1_data + rs2_data;
                                ctrl_nxt = 0;
                                PC_nxt = PC + 4;
                                write_nxt = 1;
                            end
                            3'b001:begin    //SUB
                                alu_out_nxt = 0;
                                write_rd_nxt = rs1_data - rs2_data;
                                ctrl_nxt = 0;
                                PC_nxt = PC + 4;
                                write_nxt = 1;
                            end
                            3'b010:begin    //MUL
                                //Wait!!
                                if(ready) begin
                                    alu_out_nxt = alu_out;
                                    write_rd_nxt = out[31:0];
                                    ctrl_nxt = 0;
                                    PC_nxt = PC + 4;
                                    write_nxt = 1;
                                end
                                else begin
                                    alu_out_nxt = 0;
                                    write_rd_nxt = write_rd;
                                    ctrl_nxt = 0;
                                    PC_nxt = PC;
                                    write_nxt = 0;
                                end
                            end
                            default:begin
                                alu_out_nxt = alu_out;
                                write_rd_nxt = write_rd;
                                ctrl_nxt = 0;
                                PC_nxt = PC;
                                write_nxt = write;
                            end
                        endcase
                    end
                    I:begin        //I-type
                        case(func)
                            3'b000:begin    //JALR
                                alu_out_nxt = 0;
                                write_rd_nxt = PC + 4;
                                ctrl_nxt = 0;
                                PC_nxt = rs1_data + imm;
                                write_nxt = 1;
                            end
                            3'b001:begin    //LW have some problem
                                alu_out_nxt = rs1_data + imm;
                                write_rd_nxt = write_rd;
                                ctrl_nxt = 0;
                                PC_nxt = PC;
                                write_nxt = 0;
                            end
                            3'b010:begin    //ADDI
                                alu_out_nxt = 0;
                                write_rd_nxt = rs1_data + imm;
                                ctrl_nxt = 0;
                                PC_nxt = PC + 4;
                                write_nxt = 1;
                            end
                            3'b011:begin    //SLTI
                                alu_out_nxt = 0;
                                write_rd_nxt = (rs1_data<imm) ? 1'b1 : 1'b0;
                                ctrl_nxt = 0;
                                PC_nxt = PC + 4;
                                write_nxt = 1;
                            end
                            3'b100:begin    //SLLI
                                alu_out_nxt = 0;
                                write_rd_nxt = rs1_data <<< imm[4:0];
                                ctrl_nxt = 0;
                                PC_nxt = PC + 4;
                                write_nxt = 1;
                            end
                            3'b101:begin    //SRLI
                                alu_out_nxt = 0;
                                write_rd_nxt = rs1_data >>> imm[4:0];
                                ctrl_nxt = 0;
                                PC_nxt = PC + 4;
                                write_nxt = 1;
                            end
                            default:begin
                                alu_out_nxt = alu_out;
                                write_rd_nxt = write_rd;
                                ctrl_nxt = 0;
                                PC_nxt = PC;
                                write_nxt = write;
                            end
                        endcase
                    end
                    S:begin        //S-type
                        case(func)
                            3'b000:begin    //SW 
                                alu_out_nxt = rs1_data + imm;
                                write_rd_nxt = 0;
                                ctrl_nxt = 1;
                                PC_nxt = PC;
                                write_nxt = 0;
                            end
                            default:begin
                                alu_out_nxt = alu_out;
                                write_rd_nxt = write_rd;
                                ctrl_nxt = 0;
                                PC_nxt = PC;
                                write_nxt = write;
                            end
                        endcase
                    end
                    B:begin        //B-type
                        case(func)
                            3'b000:begin    //BEQ
                                check_branch = (rs1_data==rs2_data) ? 1'b1 : 1'b0;
                                alu_out_nxt = 0;
                                write_rd_nxt = 0;
                                ctrl_nxt = 0;
                                PC_nxt = (check_branch) ? (PC+imm) : (PC+4);
                                write_nxt = 0;
                            end
                            3'b001:begin    //BNE
                                check_branch = (rs1_data!=rs2_data) ? 1'b1 : 1'b0;
                                alu_out_nxt = 0;
                                write_rd_nxt = 0;
                                ctrl_nxt = 0;
                                PC_nxt = (check_branch) ? (PC+imm) : (PC+4);
                                write_nxt = 0;
                            end
                            3'b010:begin    //BLT
                                check_branch = (rs1_data<rs2_data) ? 1'b1 : 1'b0;
                                alu_out_nxt = 0;
                                write_rd_nxt = 0;
                                ctrl_nxt = 0;
                                PC_nxt = (check_branch) ? (PC+imm) : (PC+4);
                                write_nxt = 0;
                            end
                            3'b011:begin    //BGE
                                check_branch = (rs1_data>=rs2_data) ? 1'b1 : 1'b0;
                                alu_out_nxt = 0;
                                write_rd_nxt = 0;
                                ctrl_nxt = 0;
                                PC_nxt = (check_branch) ? (PC+imm) : (PC+4);
                                write_nxt = 0;
                            end
                            default:begin
                                alu_out_nxt = alu_out;
                                write_rd_nxt = write_rd;
                                ctrl_nxt = 0;
                                PC_nxt = PC;
                                write_nxt = write;
                            end
                        endcase
                    end
                    U:begin        //U-type
                        case(func)
                            3'b000:begin    //LUI
                                alu_out_nxt = 0;
                                write_rd_nxt = imm;
                                ctrl_nxt = 0;
                                PC_nxt = PC + 4;
                                write_nxt = 1;
                            end
                            3'b001:begin    //AUIPC
                                alu_out_nxt = 0;
                                write_rd_nxt = PC + imm;
                                ctrl_nxt = 0;
                                PC_nxt = PC + 4;
                                write_nxt = 1;
                            end
                            default:begin
                                alu_out_nxt = alu_out;
                                write_rd_nxt = write_rd;
                                ctrl_nxt = 0;
                                PC_nxt = PC;
                                write_nxt = write;
                            end
                        endcase
                    end
                    J:begin        //J-type
                        case(func)
                            3'b000:begin    //JAL
                                alu_out_nxt = 0;
                                write_rd_nxt = PC + 4;
                                ctrl_nxt = 0;
                                PC_nxt = PC + imm;
                                write_nxt = 1;
                            end
                            default:begin
                                alu_out_nxt = alu_out;
                                write_rd_nxt = write_rd;
                                ctrl_nxt = 0;
                                PC_nxt = PC;
                                write_nxt = write;
                            end
                        endcase
                    end
                    default:begin
                        alu_out_nxt = alu_out;
                        write_rd_nxt = write_rd;
                        ctrl_nxt = 0;
                        PC_nxt = PC;
                        write_nxt = write;
                    end
                endcase
            end
            MW: begin
                write_rd_nxt = (type == I && func == 3'b001) ? mem_rdata_D : write_rd;
                ctrl_nxt = ctrl;
                alu_out_nxt = alu_out;
                PC_nxt = PC + 4;
                write_nxt = (type == I && func == 3'b001) ? 1 : 0;
            end
            default:begin
                alu_out_nxt = alu_out;
                write_rd_nxt = write_rd;
                ctrl_nxt = 0;
                PC_nxt = PC;
                write_nxt = 0;
            end
        endcase
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            state <= ID;
            type <= 3'b110;   // invalid
            func <= 3'b110;   // invalid
            write_rd <= 0;
            alu_out <= 0;
            write <= 0;
            ctrl <= 0;
            addr_I <= 0;
        end
        else begin
            PC <= PC_nxt;
            state <= state_nxt;
            type <= type_nxt;
            func <= func_nxt;
            write_rd <= write_rd_nxt;
            alu_out <= alu_out_nxt;
            write <= write_nxt;
            ctrl <= ctrl_nxt;
            addr_I <= addr_I_nxt;
        end 
        /*
        $display("============================================================");
        $display("PC:%H", PC);
        $display("Instruction:%H", mem_rdata_I);
        $display("RD :", rd, ", Data:%H", rd_data);
        $display("RS1:", rs1, ", Data:%H", rs1_data);
        $display("RS2:", rs2, ", Data:%H", rs2_data);
        $display("Imm:%H", imm);
        $display("ready:%b", ready);
        $display("state:", state, ", type:", type, ", func:", func);
        $display("============================================================\n");
        */
    end
endmodule


module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule

module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW3

    // Definition of ports
    input         clk, rst_n;
    input         valid, mode; // mode: 0: mulu, 1: divu
    output        ready;
    input  [31:0] in_A, in_B;
    output [63:0] out;

    // Definition of states
    parameter IDLE = 2'b00;
    parameter MUL  = 2'b01;
    parameter DIV  = 2'b10;
    parameter OUT  = 2'b11;

    // Todo: Wire and reg if needed
    reg  [ 1:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;

    // Todo: Instatiate any primitives if needed

    // Todo 5: Wire assignments
    assign  ready = (state==OUT);
    assign  out = shreg;

    // Combinational always block
    // Todo 1: Next-state logic of state machine
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid)
                    state_nxt = (mode==1) ? DIV : MUL;
                else
                    state_nxt = IDLE;
            end
            MUL : state_nxt = (counter==5'b11111) ? OUT : MUL;
            DIV : state_nxt = (counter==5'b11111) ? OUT : DIV;
            OUT : state_nxt = IDLE;       
        endcase
    end
    // Todo 2: Counter
    always @(*) begin
        case(state)
            MUL : counter_nxt = counter + 1'b1;
            DIV : counter_nxt = counter + 1'b1;
            default : counter_nxt = 0;
        endcase
    end
    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
    always @(*) begin
        case(state)
            MUL: begin 
                if (shreg[0]==1'b1) alu_out = shreg[63:32] + alu_in;
                else                alu_out = shreg[63:32];
            end
            DIV:begin
                if (shreg[62:31] >= alu_in) alu_out = shreg[62:31] - alu_in;
                else                        alu_out = shreg[62:31];
            end
            default: alu_out = 0;
        endcase
    end
    // Todo 4: Shift register
    always @(/*negedge clk or negedge rst_n*/*) begin
        case(state)
            IDLE: begin
                if (valid)begin
                    //shreg[31:0] = in_A[31:0];
                    //shreg[63:32] = 32'b0;
                    //shreg_nxt = shreg;
                    shreg_nxt[63:32] = 32'b0;
                    shreg_nxt[31:0] = in_A[31:0];
                end                  
                else
                    shreg_nxt = 0;
            end
            MUL: begin
                shreg_nxt[63:31] = alu_out[32:0];
                shreg_nxt[30:0] = shreg[31:1];
            end
            DIV: begin
                if (shreg[62:31] >= alu_in)begin
                    //shreg[62:31] = alu_out[31:0];
                    //shreg_nxt = shreg << 1;
                    shreg_nxt[63:32] = alu_out[31:0];
                    shreg_nxt[31:1] = shreg[30:0];
                    shreg_nxt[0] = 1;
                end 
                else begin
                    //shreg[62:31] = alu_out[31:0];
                    //shreg_nxt = shreg << 1;
                    shreg_nxt[63:32] = alu_out[31:0];
                    shreg_nxt[31:1] = shreg[30:0];
                    shreg_nxt[0] = 0;
                end                        
                
                
            end
            default: shreg_nxt = shreg;
        endcase
    end
    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            counter <= 0;
            shreg <= 0;
            alu_in <= 0;
        end
        else begin
            state <= state_nxt;
            counter <= counter_nxt;
            shreg <= shreg_nxt;
            alu_in <= alu_in_nxt;
        end
        //$display("State: %2d, Couter: %2d, Shreg: %16h", state, counter, shreg);
    end

endmodule