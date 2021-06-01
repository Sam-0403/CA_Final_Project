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
    wire   [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    wire   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg
    wire   [2:0] type         ; // R:0, I:1, S:2, B:3, U:4, J:5
    wire   [2:0] func         ;
    wire   [31:0]imm = 0;
    //--------------------------------------------//
    //--R------I------S------B------U------J------//
    //0:ADD    JALR   SW     BEQ    LUI    JAL
    //1:SUB    LW            BNE    AUIPC
    //2:MUL    ADDI          BLT
    //3:       SLTI          BGE
    //4:
    //5:
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
    
    // Todo: any combinational/sequential circuit
    // Instruction fetch
    // mem_rdata_I(OK)

    always @(*) begin // Instruction decode
        case(mem_rdata_I[6:0])
            7'b01101111:begin
                type = 3'b100;   // U-type
                func = 3'b000;   // LUI
                rd = mem_rdata_I[11:7];
                imm[11:0] = 0;
                imm[31:12] = mem_rdata_I[31:12];
            end
            7'b0010111:begin
                type = 3'b100;   // U-type
                func = 3'b001;   // AUIPC
                rd = mem_rdata_I[11:7];
                imm[11:0] = 0;
                imm[31:12] = mem_rdata_I[31:12];
            end
            7'b1101111:begin
                type = 3'b101;   // J-type
                func = 3'b000;   // JAL
                rd = mem_rdata_I[11:7];
                imm[20] = mem_rdata_I[31];
                imm[19:12] = mem_rdata_I[19:12];
                imm[11] = mem_rdata_I[20];
                imm[10:1] = mem_rdata_I[30:21];
            end
            7'b1100111:begin
                type = 3'b001;   // I-type
                func = 3'b000;   // JALR
                rd = mem_rdata_I[11:7];
                rs1 = mem_rdata_I[19:15];
                imm[11:0] = mem_rdata_I[31:20];
            end
            7'b1100011:begin
                type = 3'b011;   // B-type
                case(mem_rdata_I[14:12])
                    3'b000:begin
                        func = 3'b000;   // BEQ
                    end
                    3'b001:begin
                        func = 3'b001;   // BNE
                    end
                    3'b100:begin
                        func = 3'b010;   // BLT
                    end
                    3'b101:begin
                        func = 3'b011;   // BGE
                    end
                endcase
                rs1 = mem_rdata_I[19:15];
                rs2 = mem_rdata_I[24:20];
                imm[12] = mem_rdata_I[31];
                imm[11] = mem_rdata_I[7];
                imm[10:5] = mem_rdata_I[30:25];
                imm[4:1] = mem_rdata_I[11:8];
            end
            7'b0000011:begin
                type = 3'b001;   // I-type
                func = 3'b001;   // LW
                rd = mem_rdata_I[11:7];
                rs1 = mem_rdata_I[19:15];
                imm[11:0] = mem_rdata_I[31:20];
            end
            7'b0100011:begin
                type = 3'b010;   // S-type
                func = 3'b000;   // SW
                rs1 = mem_rdata_I[19:15];
                rs2 = mem_rdata_I[24:20];
                imm[11:5] = mem_rdata_I[31:25];
                imm[4:0] = mem_rdata_I[11:7];
            end
            7'b0010011:begin
                type = 3'b001;   // I-type
                case(mem_rdata_I[14:12])
                    3'b000:begin
                        func = 3'b010;   // ADDI
                    end
                    3'b010:begin
                        func = 3'b011;   // SLTI
                    end
                endcase
                rd = mem_rdata_I[11:7];
                rs1 = mem_rdata_I[19:15];
                imm[11:0] = mem_rdata_I[31:20];
            end
            7'b0110011:begin
                type = 3'b001;   // I-type
                case(mem_rdata_I[31:25])
                    7'b0000000:begin
                        func = 3'b000;   // ADD
                    end
                    7'b0100000:begin
                        func = 3'b001;   // SUB
                    end
                    7'b0000001:begin
                        func = 3'b010;   // MUL
                    end
                endcase
                rd = mem_rdata_I[11:7];
                rs1 = mem_rdata_I[19:15];
                rs2 = mem_rdata_I[24:20];
            end
        endcase
    end

    always @(*) begin // Execution
        case(type)
            3'b000:begin        //R-type
                regWrite = 0;
                case(func)
                    3'b000:begin    //ADD
                        rd_data = rs1_data + rs2_data;
                    end
                    3'b001:begin    //SUB
                        rd_data = rs1_data - rs2_data;
                    end
                    3'b010:begin    //MUL
                        //Wait!!
                    end
                endcase
            end
            3'b001:begin        //I-type
                case(func)
                    3'b000:begin    //JALR
                        
                    end
                    3'b001:begin    //LW
                        
                    end
                    3'b010:begin    //ADDI
                        
                    end
                    3'b011:begin    //SLTI
                        
                    end
                endcase
            end
            3'b010:begin        //S-type
                case(func)
                    3'b000:begin    //SW
                        
                    end
                endcase
            end
            3'b011:begin        //B-type
                case(func)
                    3'b000:begin    //BEQ
                        
                    end
                    3'b001:begin    //BNE
                        
                    end
                    3'b010:begin    //BLT
                        
                    end
                    3'b011:begin    //BGE
                        
                    end
                endcase
            end
            3'b100:begin        //U-type
                case(func)
                    3'b000:begin    //LUI
                        
                    end
                    3'b001:begin    //AUIPC
                        
                    end
                endcase
            end
            3'b101:begin        //J-type
                case(func)
                    3'b000:begin    //JAL
                        
                    end
                endcase
            end
        endcase
    end

    always @(*) begin // Memory access
        case(type)
            3'b001:begin        //I-type
                case(func)
                    3'b000:begin    //JALR
                        
                    end
                    3'b001:begin    //LW
                        
                    end
                    3'b010:begin    //ADDI
                        
                    end
                    3'b011:begin    //SLTI
                        
                    end
                endcase
            end
            3'b010:begin        //S-type
                case(func)
                    3'b000:begin    //SW
                        
                    end
                endcase
            end
            3'b100:begin        //U-type
                case(func)
                    3'b000:begin    //LUI
                        
                    end
                    3'b001:begin    //AUIPC
                        
                    end
                endcase
            end
            3'b101:begin        //J-type
                case(func)
                    3'b000:begin    //JAL
                        
                    end
                endcase
            end
        endcase
    end

    always @(*) begin // Write back 
        
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            
        end
        else begin
            PC <= PC_nxt;
            
        end
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