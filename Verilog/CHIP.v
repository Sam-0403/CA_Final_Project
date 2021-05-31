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
                type = 3'b100   // U-type
                func = 3'b000   // LUI
            end
            7'b0010111:begin
                type = 3'b100   // U-type
                func = 3'b001   // AUIPC
            end
            7'b1101111:begin
                type = 3'b101   // J-type
                func = 3'b000   // JAL
            end
            7'b1100111:begin
                type = 3'b001   // I-type
                func = 3'b000   // JALR
            end
            7'b1100011:begin
                type = 3'b011   // B-type
                case(mem_rdata_I[14:12])
                    3'b000:begin
                        func = 3'b000   // BEQ
                    end
                    3'b001:begin
                        func = 3'b001   // BNE
                    end
                    3'b100:begin
                        func = 3'b010   // BLT
                    end
                    3'b101:begin
                        func = 3'b011   // BGE
                    end
                endcase
            end
            7'b0000011:begin
                type = 3'b001   // I-type
                func = 3'b001   // LW
            end
            7'b0100011:begin
                type = 3'b010   // S-type
                func = 3'b000   // SW
            end
            7'b0010011:begin
                type = 3'b001   // I-type
                case(mem_rdata_I[14:12])
                    3'b000:begin
                        func = 3'b010   // ADDI
                    end
                    3'b010:begin
                        func = 3'b011   // SLTI
                    end
                endcase
            end
            7'b0110011:begin
                type = 3'b001   // I-type
                case(mem_rdata_I[31:25])
                    7'b0000000:begin
                        func = 3'b000   // ADD
                    end
                    7'b0100000:begin
                        func = 3'b001   // SUB
                    end
                    7'b0000001:begin
                        func = 3'b010   // MUL
                    end
                endcase
            end
        endcase
    end

    always @(*) begin // Execution
        
    end

    always @(*) begin // Memory access
        
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

endmodule