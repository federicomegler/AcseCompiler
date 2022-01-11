      .data
_i:   .WORD 0
      .text
      ADDI R1 R0 #10       /* line 4 */
      STORE R1 _i
L1:   LOAD R1 _i
      SUBI R2 R1 #0
      STORE R1 _i
      SGT R2 0
      ANDB R2 R2 R2
      BEQ L2
      BT L3
L4:   LOAD R1 _i
      SUBI R2 R1 #1
      ADD R1 R0 R2
      STORE R1 _i
      BT L1
L3:   LOAD R1 _i
      WRITE R1 0           /* line 5 */
      STORE R1 _i
      BT L4                /* line 6 */
L2:   HALT                 /* line 9 */
