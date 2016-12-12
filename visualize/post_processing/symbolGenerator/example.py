# main()
# SSSS Calling function main
#fslice_value = 0
t1=V(0, 1) # Taint<1, 0, 0>
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
# parse_arguments()
# SSSS Calling function parse_arguments
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t2=V(1, 2) # Taint<2, 0, 0>
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_UGT')
t3=A("sub",t0,t0, 3)
#fslice_value = 1
ICMP(t3,t2,'ICMP_UGT')
# SSSS Returning back from functionparse_arguments
#fslice_value = 0
# testfs_init_super_block()
# SSSS Calling function testfs_init_super_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 72
t4=V(72, 4) # Taint<4, 0, 0>
t5=M(72, 0, 5,t4)
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1052674
t6=V(1052674, 6) # Taint<6, 0, 0>
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
ICMP(t0,t0,'ICMP_EQ')
#fslice_value = 0
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 3:read_blocks()--->testfs_init_super_block()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t7=V(64, 7) # Taint<7, 0, 0>
t8=A("mul",t1,t7, 8)
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
t9=A("add",t1,t1, 9)
#fslice_value = 64
#gBlockTAINT 10
t10=B(64,0,t7,t9, 10) # GetBlock(64, 0) r
#fslice_value = 1
t11=A("add",t1,t2, 11)
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
t5[0]=t10[0] # fslice_memmove
t5[1]=t10[1] # fslice_memmove
t5[2]=t10[2] # fslice_memmove
t5[3]=t10[3] # fslice_memmove
t5[4]=t10[4] # fslice_memmove
t5[5]=t10[5] # fslice_memmove
t5[6]=t10[6] # fslice_memmove
t5[7]=t10[7] # fslice_memmove
t5[8]=t10[8] # fslice_memmove
t5[9]=t10[9] # fslice_memmove
t5[10]=t10[10] # fslice_memmove
t5[11]=t10[11] # fslice_memmove
t5[12]=t10[12] # fslice_memmove
t5[13]=t10[13] # fslice_memmove
t5[14]=t10[14] # fslice_memmove
t5[15]=t10[15] # fslice_memmove
t5[16]=t10[16] # fslice_memmove
t5[17]=t10[17] # fslice_memmove
t5[18]=t10[18] # fslice_memmove
t5[19]=t10[19] # fslice_memmove
t5[20]=t10[20] # fslice_memmove
t5[21]=t10[21] # fslice_memmove
t5[22]=t10[22] # fslice_memmove
t5[23]=t10[23] # fslice_memmove
t5[24]=t10[24] # fslice_memmove
t5[25]=t10[25] # fslice_memmove
t5[26]=t10[26] # fslice_memmove
t5[27]=t10[27] # fslice_memmove
#DSTRUCT:t10,0:Size|28
#testfs_init_super_block:&sb->sb
#testfs_init_super_block:block
#fslice_value = 512
t12=V(512, 12) # Taint<12, 0, 0>
# bitmap_create()
# SSSS Calling function bitmap_create
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 16
t13=V(16, 13) # Taint<13, 0, 0>
t14=M(16, 0, 14,t13)
#fslice_value = 0
ICMP(t0,t0,'ICMP_EQ')
#fslice_value = 8
t15=V(8, 15) # Taint<15, 0, 0>
t16=A("add",t12,t15, 16)
#fslice_value = 1
t17=A("sub",t16,t2, 17)
#fslice_value = 8
t18=A("udiv",t17,t15, 18)
#fslice_value = 1
t19=A("mul",t18,t2, 19)
t20=M(64, 0, 20,t19)
ICMP(t0,t0,'ICMP_EQ')
#fslice_value = 1
#bitmap_create:b->v
#fslice_value = 8
t21=A("udiv",t12,t15, 21)
ICMP(t21,t18,'ICMP_ULE')
#fslice_value = 0
# SSSS Returning back from functionbitmap_create
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# bitmap_getdata()
# SSSS Calling function bitmap_getdata
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functionbitmap_getdata
 #YYY assigned new taint id = 10 taint id checked for = 10
t22=O(t10,22,t10[0],t10[1],t10[2],t10[3]) # Load(32700640, 4)
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 3:read_blocks()--->testfs_init_super_block()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t23=A("mul",t22,t7, 23)#SWITCH 22 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
t24=A("add",t22,t1, 24)#SWITCH 22 0
#fslice_value = 64
#gBlockTAINT 25
t25=B(64,1,t7,t24, 25) # GetBlock(64, 1) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
#fslice_value = 1024
t26=V(1024, 26) # Taint<26, 0, 0>
# bitmap_create()
# SSSS Calling function bitmap_create
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 16
t27=M(16, 0, 27,t13)
#fslice_value = 0
ICMP(t0,t0,'ICMP_EQ')
#fslice_value = 8
t28=A("add",t26,t15, 28)
#fslice_value = 1
t29=A("sub",t28,t2, 29)
#fslice_value = 8
t30=A("udiv",t29,t15, 30)
#fslice_value = 1
t31=A("mul",t30,t2, 31)
t32=M(128, 0, 32,t31)
ICMP(t0,t0,'ICMP_EQ')
#fslice_value = 1
#bitmap_create:b->v
#fslice_value = 8
t33=A("udiv",t26,t15, 33)
ICMP(t33,t30,'ICMP_ULE')
#fslice_value = 0
# SSSS Returning back from functionbitmap_create
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# bitmap_getdata()
# SSSS Calling function bitmap_getdata
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functionbitmap_getdata
 #YYY assigned new taint id = 10 taint id checked for = 10
t34=O(t10,34,t10[4],t10[5],t10[6],t10[7]) # Load(32700644, 4)
#fslice_value = 2
t35=V(2, 35) # Taint<35, 0, 0>
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 3:read_blocks()--->testfs_init_super_block()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t36=A("mul",t34,t7, 36)#SWITCH 34 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t35,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t35,'ICMP_ULE')
#fslice_value = 64
t37=A("add",t34,t1, 37)#SWITCH 34 0
#fslice_value = 64
#gBlockTAINT 38
t38=B(64,2,t7,t37, 38) # GetBlock(64, 2) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t35,'ICMP_ULE')
#fslice_value = 64
t39=A("mul",t11,t7, 39)
t40=A("add",t34,t11, 40)#SWITCH 34 0
#fslice_value = 64
#gBlockTAINT 41
t41=B(64,3,t7,t40, 41) # GetBlock(64, 3) r
#fslice_value = 1
t42=A("add",t11,t2, 42)
#fslice_value = 0
ICMP(t42,t35,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
#fslice_value = 3840
t43=V(3840, 43) # Taint<43, 0, 0>
t44=M(3840, 0, 44,t43)
ICMP(t0,t0,'ICMP_UGT')
 #YYY assigned new taint id = 10 taint id checked for = 10
t45=O(t10,45,t10[8],t10[9],t10[10],t10[11]) # Load(32700648, 4)
#fslice_value = 60
t46=V(60, 46) # Taint<46, 0, 0>
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 3:read_blocks()--->testfs_init_super_block()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t47=A("mul",t45,t7, 47)#SWITCH 45 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t46,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t46,'ICMP_ULE')
#fslice_value = 64
t48=A("add",t45,t1, 48)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 49
t49=B(64,4,t7,t48, 49) # GetBlock(64, 4) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t46,'ICMP_ULE')
#fslice_value = 64
t50=A("add",t45,t11, 50)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 51
t51=B(64,5,t7,t50, 51) # GetBlock(64, 5) r
#fslice_value = 1
#fslice_value = 0
ICMP(t42,t46,'ICMP_ULE')
#fslice_value = 64
t52=A("mul",t42,t7, 52)
t53=A("add",t45,t42, 53)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 54
t54=B(64,6,t7,t53, 54) # GetBlock(64, 6) r
#fslice_value = 1
t55=A("add",t42,t2, 55)
#fslice_value = 0
ICMP(t55,t46,'ICMP_ULE')
#fslice_value = 64
t56=A("mul",t55,t7, 56)
t57=A("add",t45,t55, 57)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 58
t58=B(64,7,t7,t57, 58) # GetBlock(64, 7) r
#fslice_value = 1
t59=A("add",t55,t2, 59)
#fslice_value = 0
ICMP(t59,t46,'ICMP_ULE')
#fslice_value = 64
t60=A("mul",t59,t7, 60)
t61=A("add",t45,t59, 61)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 62
t62=B(64,8,t7,t61, 62) # GetBlock(64, 8) r
#fslice_value = 1
t63=A("add",t59,t2, 63)
#fslice_value = 0
ICMP(t63,t46,'ICMP_ULE')
#fslice_value = 64
t64=A("mul",t63,t7, 64)
t65=A("add",t45,t63, 65)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 66
t66=B(64,9,t7,t65, 66) # GetBlock(64, 9) r
#fslice_value = 1
t67=A("add",t63,t2, 67)
#fslice_value = 0
ICMP(t67,t46,'ICMP_ULE')
#fslice_value = 64
t68=A("mul",t67,t7, 68)
t69=A("add",t45,t67, 69)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 70
t70=B(64,10,t7,t69, 70) # GetBlock(64, 10) r
#fslice_value = 1
t71=A("add",t67,t2, 71)
#fslice_value = 0
ICMP(t71,t46,'ICMP_ULE')
#fslice_value = 64
t72=A("mul",t71,t7, 72)
t73=A("add",t45,t71, 73)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 74
t74=B(64,11,t7,t73, 74) # GetBlock(64, 11) r
#fslice_value = 1
t75=A("add",t71,t2, 75)
#fslice_value = 0
ICMP(t75,t46,'ICMP_ULE')
#fslice_value = 64
t76=A("mul",t75,t7, 76)
t77=A("add",t45,t75, 77)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 78
t78=B(64,12,t7,t77, 78) # GetBlock(64, 12) r
#fslice_value = 1
t79=A("add",t75,t2, 79)
#fslice_value = 0
ICMP(t79,t46,'ICMP_ULE')
#fslice_value = 64
t80=A("mul",t79,t7, 80)
t81=A("add",t45,t79, 81)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 82
t82=B(64,13,t7,t81, 82) # GetBlock(64, 13) r
#fslice_value = 1
t83=A("add",t79,t2, 83)
#fslice_value = 0
ICMP(t83,t46,'ICMP_ULE')
#fslice_value = 64
t84=A("mul",t83,t7, 84)
t85=A("add",t45,t83, 85)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 86
t86=B(64,14,t7,t85, 86) # GetBlock(64, 14) r
#fslice_value = 1
t87=A("add",t83,t2, 87)
#fslice_value = 0
ICMP(t87,t46,'ICMP_ULE')
#fslice_value = 64
t88=A("mul",t87,t7, 88)
t89=A("add",t45,t87, 89)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 90
t90=B(64,15,t7,t89, 90) # GetBlock(64, 15) r
#fslice_value = 1
t91=A("add",t87,t2, 91)
#fslice_value = 0
ICMP(t91,t46,'ICMP_ULE')
#fslice_value = 64
t92=A("mul",t91,t7, 92)
t93=A("add",t45,t91, 93)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 94
t94=B(64,16,t7,t93, 94) # GetBlock(64, 16) r
#fslice_value = 1
t95=A("add",t91,t2, 95)
#fslice_value = 0
ICMP(t95,t46,'ICMP_ULE')
#fslice_value = 64
t96=A("mul",t95,t7, 96)
t97=A("add",t45,t95, 97)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 98
t98=B(64,17,t7,t97, 98) # GetBlock(64, 17) r
#fslice_value = 1
t99=A("add",t95,t2, 99)
#fslice_value = 0
ICMP(t99,t46,'ICMP_ULE')
#fslice_value = 64
t100=A("mul",t99,t7, 100)
t101=A("add",t45,t99, 101)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 102
t102=B(64,18,t7,t101, 102) # GetBlock(64, 18) r
#fslice_value = 1
t103=A("add",t99,t2, 103)
#fslice_value = 0
ICMP(t103,t46,'ICMP_ULE')
#fslice_value = 64
t104=A("mul",t103,t7, 104)
t105=A("add",t45,t103, 105)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 106
t106=B(64,19,t7,t105, 106) # GetBlock(64, 19) r
#fslice_value = 1
t107=A("add",t103,t2, 107)
#fslice_value = 0
ICMP(t107,t46,'ICMP_ULE')
#fslice_value = 64
t108=A("mul",t107,t7, 108)
t109=A("add",t45,t107, 109)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 110
t110=B(64,20,t7,t109, 110) # GetBlock(64, 20) r
#fslice_value = 1
t111=A("add",t107,t2, 111)
#fslice_value = 0
ICMP(t111,t46,'ICMP_ULE')
#fslice_value = 64
t112=A("mul",t111,t7, 112)
t113=A("add",t45,t111, 113)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 114
t114=B(64,21,t7,t113, 114) # GetBlock(64, 21) r
#fslice_value = 1
t115=A("add",t111,t2, 115)
#fslice_value = 0
ICMP(t115,t46,'ICMP_ULE')
#fslice_value = 64
t116=A("mul",t115,t7, 116)
t117=A("add",t45,t115, 117)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 118
t118=B(64,22,t7,t117, 118) # GetBlock(64, 22) r
#fslice_value = 1
t119=A("add",t115,t2, 119)
#fslice_value = 0
ICMP(t119,t46,'ICMP_ULE')
#fslice_value = 64
t120=A("mul",t119,t7, 120)
t121=A("add",t45,t119, 121)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 122
t122=B(64,23,t7,t121, 122) # GetBlock(64, 23) r
#fslice_value = 1
t123=A("add",t119,t2, 123)
#fslice_value = 0
ICMP(t123,t46,'ICMP_ULE')
#fslice_value = 64
t124=A("mul",t123,t7, 124)
t125=A("add",t45,t123, 125)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 126
t126=B(64,24,t7,t125, 126) # GetBlock(64, 24) r
#fslice_value = 1
t127=A("add",t123,t2, 127)
#fslice_value = 0
ICMP(t127,t46,'ICMP_ULE')
#fslice_value = 64
t128=A("mul",t127,t7, 128)
t129=A("add",t45,t127, 129)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 130
t130=B(64,25,t7,t129, 130) # GetBlock(64, 25) r
#fslice_value = 1
t131=A("add",t127,t2, 131)
#fslice_value = 0
ICMP(t131,t46,'ICMP_ULE')
#fslice_value = 64
t132=A("mul",t131,t7, 132)
t133=A("add",t45,t131, 133)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 134
t134=B(64,26,t7,t133, 134) # GetBlock(64, 26) r
#fslice_value = 1
t135=A("add",t131,t2, 135)
#fslice_value = 0
ICMP(t135,t46,'ICMP_ULE')
#fslice_value = 64
t136=A("mul",t135,t7, 136)
t137=A("add",t45,t135, 137)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 138
t138=B(64,27,t7,t137, 138) # GetBlock(64, 27) r
#fslice_value = 1
t139=A("add",t135,t2, 139)
#fslice_value = 0
ICMP(t139,t46,'ICMP_ULE')
#fslice_value = 64
t140=A("mul",t139,t7, 140)
t141=A("add",t45,t139, 141)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 142
t142=B(64,28,t7,t141, 142) # GetBlock(64, 28) r
#fslice_value = 1
t143=A("add",t139,t2, 143)
#fslice_value = 0
ICMP(t143,t46,'ICMP_ULE')
#fslice_value = 64
t144=A("mul",t143,t7, 144)
t145=A("add",t45,t143, 145)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 146
t146=B(64,29,t7,t145, 146) # GetBlock(64, 29) r
#fslice_value = 1
t147=A("add",t143,t2, 147)
#fslice_value = 0
ICMP(t147,t46,'ICMP_ULE')
#fslice_value = 64
t148=A("mul",t147,t7, 148)
t149=A("add",t45,t147, 149)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 150
t150=B(64,30,t7,t149, 150) # GetBlock(64, 30) r
#fslice_value = 1
t151=A("add",t147,t2, 151)
#fslice_value = 0
ICMP(t151,t46,'ICMP_ULE')
#fslice_value = 64
t152=A("mul",t151,t7, 152)
t153=A("add",t45,t151, 153)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 154
t154=B(64,31,t7,t153, 154) # GetBlock(64, 31) r
#fslice_value = 1
t155=A("add",t151,t2, 155)
#fslice_value = 0
ICMP(t155,t46,'ICMP_ULE')
#fslice_value = 64
t156=A("mul",t155,t7, 156)
t157=A("add",t45,t155, 157)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 158
t158=B(64,32,t7,t157, 158) # GetBlock(64, 32) r
#fslice_value = 1
t159=A("add",t155,t2, 159)
#fslice_value = 0
ICMP(t159,t46,'ICMP_ULE')
#fslice_value = 64
t160=A("mul",t159,t7, 160)
t161=A("add",t45,t159, 161)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 162
t162=B(64,33,t7,t161, 162) # GetBlock(64, 33) r
#fslice_value = 1
t163=A("add",t159,t2, 163)
#fslice_value = 0
ICMP(t163,t46,'ICMP_ULE')
#fslice_value = 64
t164=A("mul",t163,t7, 164)
t165=A("add",t45,t163, 165)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 166
t166=B(64,34,t7,t165, 166) # GetBlock(64, 34) r
#fslice_value = 1
t167=A("add",t163,t2, 167)
#fslice_value = 0
ICMP(t167,t46,'ICMP_ULE')
#fslice_value = 64
t168=A("mul",t167,t7, 168)
t169=A("add",t45,t167, 169)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 170
t170=B(64,35,t7,t169, 170) # GetBlock(64, 35) r
#fslice_value = 1
t171=A("add",t167,t2, 171)
#fslice_value = 0
ICMP(t171,t46,'ICMP_ULE')
#fslice_value = 64
t172=A("mul",t171,t7, 172)
t173=A("add",t45,t171, 173)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 174
t174=B(64,36,t7,t173, 174) # GetBlock(64, 36) r
#fslice_value = 1
t175=A("add",t171,t2, 175)
#fslice_value = 0
ICMP(t175,t46,'ICMP_ULE')
#fslice_value = 64
t176=A("mul",t175,t7, 176)
t177=A("add",t45,t175, 177)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 178
t178=B(64,37,t7,t177, 178) # GetBlock(64, 37) r
#fslice_value = 1
t179=A("add",t175,t2, 179)
#fslice_value = 0
ICMP(t179,t46,'ICMP_ULE')
#fslice_value = 64
t180=A("mul",t179,t7, 180)
t181=A("add",t45,t179, 181)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 182
t182=B(64,38,t7,t181, 182) # GetBlock(64, 38) r
#fslice_value = 1
t183=A("add",t179,t2, 183)
#fslice_value = 0
ICMP(t183,t46,'ICMP_ULE')
#fslice_value = 64
t184=A("mul",t183,t7, 184)
t185=A("add",t45,t183, 185)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 186
t186=B(64,39,t7,t185, 186) # GetBlock(64, 39) r
#fslice_value = 1
t187=A("add",t183,t2, 187)
#fslice_value = 0
ICMP(t187,t46,'ICMP_ULE')
#fslice_value = 64
t188=A("mul",t187,t7, 188)
t189=A("add",t45,t187, 189)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 190
t190=B(64,40,t7,t189, 190) # GetBlock(64, 40) r
#fslice_value = 1
t191=A("add",t187,t2, 191)
#fslice_value = 0
ICMP(t191,t46,'ICMP_ULE')
#fslice_value = 64
t192=A("mul",t191,t7, 192)
t193=A("add",t45,t191, 193)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 194
t194=B(64,41,t7,t193, 194) # GetBlock(64, 41) r
#fslice_value = 1
t195=A("add",t191,t2, 195)
#fslice_value = 0
ICMP(t195,t46,'ICMP_ULE')
#fslice_value = 64
t196=A("mul",t195,t7, 196)
t197=A("add",t45,t195, 197)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 198
t198=B(64,42,t7,t197, 198) # GetBlock(64, 42) r
#fslice_value = 1
t199=A("add",t195,t2, 199)
#fslice_value = 0
ICMP(t199,t46,'ICMP_ULE')
#fslice_value = 64
t200=A("mul",t199,t7, 200)
t201=A("add",t45,t199, 201)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 202
t202=B(64,43,t7,t201, 202) # GetBlock(64, 43) r
#fslice_value = 1
t203=A("add",t199,t2, 203)
#fslice_value = 0
ICMP(t203,t46,'ICMP_ULE')
#fslice_value = 64
t204=A("mul",t203,t7, 204)
t205=A("add",t45,t203, 205)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 206
t206=B(64,44,t7,t205, 206) # GetBlock(64, 44) r
#fslice_value = 1
t207=A("add",t203,t2, 207)
#fslice_value = 0
ICMP(t207,t46,'ICMP_ULE')
#fslice_value = 64
t208=A("mul",t207,t7, 208)
t209=A("add",t45,t207, 209)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 210
t210=B(64,45,t7,t209, 210) # GetBlock(64, 45) r
#fslice_value = 1
t211=A("add",t207,t2, 211)
#fslice_value = 0
ICMP(t211,t46,'ICMP_ULE')
#fslice_value = 64
t212=A("mul",t211,t7, 212)
t213=A("add",t45,t211, 213)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 214
t214=B(64,46,t7,t213, 214) # GetBlock(64, 46) r
#fslice_value = 1
t215=A("add",t211,t2, 215)
#fslice_value = 0
ICMP(t215,t46,'ICMP_ULE')
#fslice_value = 64
t216=A("mul",t215,t7, 216)
t217=A("add",t45,t215, 217)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 218
t218=B(64,47,t7,t217, 218) # GetBlock(64, 47) r
#fslice_value = 1
t219=A("add",t215,t2, 219)
#fslice_value = 0
ICMP(t219,t46,'ICMP_ULE')
#fslice_value = 64
t220=A("mul",t219,t7, 220)
t221=A("add",t45,t219, 221)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 222
t222=B(64,48,t7,t221, 222) # GetBlock(64, 48) r
#fslice_value = 1
t223=A("add",t219,t2, 223)
#fslice_value = 0
ICMP(t223,t46,'ICMP_ULE')
#fslice_value = 64
t224=A("mul",t223,t7, 224)
t225=A("add",t45,t223, 225)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 226
t226=B(64,49,t7,t225, 226) # GetBlock(64, 49) r
#fslice_value = 1
t227=A("add",t223,t2, 227)
#fslice_value = 0
ICMP(t227,t46,'ICMP_ULE')
#fslice_value = 64
t228=A("mul",t227,t7, 228)
t229=A("add",t45,t227, 229)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 230
t230=B(64,50,t7,t229, 230) # GetBlock(64, 50) r
#fslice_value = 1
t231=A("add",t227,t2, 231)
#fslice_value = 0
ICMP(t231,t46,'ICMP_ULE')
#fslice_value = 64
t232=A("mul",t231,t7, 232)
t233=A("add",t45,t231, 233)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 234
t234=B(64,51,t7,t233, 234) # GetBlock(64, 51) r
#fslice_value = 1
t235=A("add",t231,t2, 235)
#fslice_value = 0
ICMP(t235,t46,'ICMP_ULE')
#fslice_value = 64
t236=A("mul",t235,t7, 236)
t237=A("add",t45,t235, 237)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 238
t238=B(64,52,t7,t237, 238) # GetBlock(64, 52) r
#fslice_value = 1
t239=A("add",t235,t2, 239)
#fslice_value = 0
ICMP(t239,t46,'ICMP_ULE')
#fslice_value = 64
t240=A("mul",t239,t7, 240)
t241=A("add",t45,t239, 241)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 242
t242=B(64,53,t7,t241, 242) # GetBlock(64, 53) r
#fslice_value = 1
t243=A("add",t239,t2, 243)
#fslice_value = 0
ICMP(t243,t46,'ICMP_ULE')
#fslice_value = 64
t244=A("mul",t243,t7, 244)
t245=A("add",t45,t243, 245)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 246
t246=B(64,54,t7,t245, 246) # GetBlock(64, 54) r
#fslice_value = 1
t247=A("add",t243,t2, 247)
#fslice_value = 0
ICMP(t247,t46,'ICMP_ULE')
#fslice_value = 64
t248=A("mul",t247,t7, 248)
t249=A("add",t45,t247, 249)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 250
t250=B(64,55,t7,t249, 250) # GetBlock(64, 55) r
#fslice_value = 1
t251=A("add",t247,t2, 251)
#fslice_value = 0
ICMP(t251,t46,'ICMP_ULE')
#fslice_value = 64
t252=A("mul",t251,t7, 252)
t253=A("add",t45,t251, 253)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 254
t254=B(64,56,t7,t253, 254) # GetBlock(64, 56) r
#fslice_value = 1
t255=A("add",t251,t2, 255)
#fslice_value = 0
ICMP(t255,t46,'ICMP_ULE')
#fslice_value = 64
t256=A("mul",t255,t7, 256)
t257=A("add",t45,t255, 257)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 258
t258=B(64,57,t7,t257, 258) # GetBlock(64, 57) r
#fslice_value = 1
t259=A("add",t255,t2, 259)
#fslice_value = 0
ICMP(t259,t46,'ICMP_ULE')
#fslice_value = 64
t260=A("mul",t259,t7, 260)
t261=A("add",t45,t259, 261)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 262
t262=B(64,58,t7,t261, 262) # GetBlock(64, 58) r
#fslice_value = 1
t263=A("add",t259,t2, 263)
#fslice_value = 0
ICMP(t263,t46,'ICMP_ULE')
#fslice_value = 64
t264=A("mul",t263,t7, 264)
t265=A("add",t45,t263, 265)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 266
t266=B(64,59,t7,t265, 266) # GetBlock(64, 59) r
#fslice_value = 1
t267=A("add",t263,t2, 267)
#fslice_value = 0
ICMP(t267,t46,'ICMP_ULE')
#fslice_value = 64
t268=A("mul",t267,t7, 268)
t269=A("add",t45,t267, 269)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 270
t270=B(64,60,t7,t269, 270) # GetBlock(64, 60) r
#fslice_value = 1
t271=A("add",t267,t2, 271)
#fslice_value = 0
ICMP(t271,t46,'ICMP_ULE')
#fslice_value = 64
t272=A("mul",t271,t7, 272)
t273=A("add",t45,t271, 273)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 274
t274=B(64,61,t7,t273, 274) # GetBlock(64, 61) r
#fslice_value = 1
t275=A("add",t271,t2, 275)
#fslice_value = 0
ICMP(t275,t46,'ICMP_ULE')
#fslice_value = 64
t276=A("mul",t275,t7, 276)
t277=A("add",t45,t275, 277)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 278
t278=B(64,62,t7,t277, 278) # GetBlock(64, 62) r
#fslice_value = 1
t279=A("add",t275,t2, 279)
#fslice_value = 0
ICMP(t279,t46,'ICMP_ULE')
#fslice_value = 64
t280=A("mul",t279,t7, 280)
t281=A("add",t45,t279, 281)#SWITCH 45 0
#fslice_value = 64
#gBlockTAINT 282
t282=B(64,63,t7,t281, 282) # GetBlock(64, 63) r
#fslice_value = 1
t283=A("add",t279,t2, 283)
#fslice_value = 0
ICMP(t283,t46,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
#fslice_value = 0
# inode_hash_init()
# SSSS Calling function inode_hash_init
#fslice_value = 0
#fslice_value = 2048
t284=V(2048, 284) # Taint<284, 0, 0>
t285=M(2048, 0, 285,t284)
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 256
t286=V(256, 286) # Taint<286, 0, 0>
ICMP(t1,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t11,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t42,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t55,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t59,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t63,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t67,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t71,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t75,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t79,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t83,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t87,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t91,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t95,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t99,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t103,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t107,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t111,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t115,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t119,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t123,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t127,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t131,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t135,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t139,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t143,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t147,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t151,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t155,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t159,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t163,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t167,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t171,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t175,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t179,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t183,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t187,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t191,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t195,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t199,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t203,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t207,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t211,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t215,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t219,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t223,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t227,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t231,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t235,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t239,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t243,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t247,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t251,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t255,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t259,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t263,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t267,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t271,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t275,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t279,t286,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t283,t286,'ICMP_ULE')
#fslice_value = 1
t287=A("add",t283,t2, 287)
#fslice_value = 0
#fslice_value = 256
ICMP(t287,t286,'ICMP_ULE')
#fslice_value = 1
t288=A("add",t287,t2, 288)
#fslice_value = 0
#fslice_value = 256
ICMP(t288,t286,'ICMP_ULE')
#fslice_value = 1
t289=A("add",t288,t2, 289)
#fslice_value = 0
#fslice_value = 256
ICMP(t289,t286,'ICMP_ULE')
#fslice_value = 1
t290=A("add",t289,t2, 290)
#fslice_value = 0
#fslice_value = 256
ICMP(t290,t286,'ICMP_ULE')
#fslice_value = 1
t291=A("add",t290,t2, 291)
#fslice_value = 0
#fslice_value = 256
ICMP(t291,t286,'ICMP_ULE')
#fslice_value = 1
t292=A("add",t291,t2, 292)
#fslice_value = 0
#fslice_value = 256
ICMP(t292,t286,'ICMP_ULE')
#fslice_value = 1
t293=A("add",t292,t2, 293)
#fslice_value = 0
#fslice_value = 256
ICMP(t293,t286,'ICMP_ULE')
#fslice_value = 1
t294=A("add",t293,t2, 294)
#fslice_value = 0
#fslice_value = 256
ICMP(t294,t286,'ICMP_ULE')
#fslice_value = 1
t295=A("add",t294,t2, 295)
#fslice_value = 0
#fslice_value = 256
ICMP(t295,t286,'ICMP_ULE')
#fslice_value = 1
t296=A("add",t295,t2, 296)
#fslice_value = 0
#fslice_value = 256
ICMP(t296,t286,'ICMP_ULE')
#fslice_value = 1
t297=A("add",t296,t2, 297)
#fslice_value = 0
#fslice_value = 256
ICMP(t297,t286,'ICMP_ULE')
#fslice_value = 1
t298=A("add",t297,t2, 298)
#fslice_value = 0
#fslice_value = 256
ICMP(t298,t286,'ICMP_ULE')
#fslice_value = 1
t299=A("add",t298,t2, 299)
#fslice_value = 0
#fslice_value = 256
ICMP(t299,t286,'ICMP_ULE')
#fslice_value = 1
t300=A("add",t299,t2, 300)
#fslice_value = 0
#fslice_value = 256
ICMP(t300,t286,'ICMP_ULE')
#fslice_value = 1
t301=A("add",t300,t2, 301)
#fslice_value = 0
#fslice_value = 256
ICMP(t301,t286,'ICMP_ULE')
#fslice_value = 1
t302=A("add",t301,t2, 302)
#fslice_value = 0
#fslice_value = 256
ICMP(t302,t286,'ICMP_ULE')
#fslice_value = 1
t303=A("add",t302,t2, 303)
#fslice_value = 0
#fslice_value = 256
ICMP(t303,t286,'ICMP_ULE')
#fslice_value = 1
t304=A("add",t303,t2, 304)
#fslice_value = 0
#fslice_value = 256
ICMP(t304,t286,'ICMP_ULE')
#fslice_value = 1
t305=A("add",t304,t2, 305)
#fslice_value = 0
#fslice_value = 256
ICMP(t305,t286,'ICMP_ULE')
#fslice_value = 1
t306=A("add",t305,t2, 306)
#fslice_value = 0
#fslice_value = 256
ICMP(t306,t286,'ICMP_ULE')
#fslice_value = 1
t307=A("add",t306,t2, 307)
#fslice_value = 0
#fslice_value = 256
ICMP(t307,t286,'ICMP_ULE')
#fslice_value = 1
t308=A("add",t307,t2, 308)
#fslice_value = 0
#fslice_value = 256
ICMP(t308,t286,'ICMP_ULE')
#fslice_value = 1
t309=A("add",t308,t2, 309)
#fslice_value = 0
#fslice_value = 256
ICMP(t309,t286,'ICMP_ULE')
#fslice_value = 1
t310=A("add",t309,t2, 310)
#fslice_value = 0
#fslice_value = 256
ICMP(t310,t286,'ICMP_ULE')
#fslice_value = 1
t311=A("add",t310,t2, 311)
#fslice_value = 0
#fslice_value = 256
ICMP(t311,t286,'ICMP_ULE')
#fslice_value = 1
t312=A("add",t311,t2, 312)
#fslice_value = 0
#fslice_value = 256
ICMP(t312,t286,'ICMP_ULE')
#fslice_value = 1
t313=A("add",t312,t2, 313)
#fslice_value = 0
#fslice_value = 256
ICMP(t313,t286,'ICMP_ULE')
#fslice_value = 1
t314=A("add",t313,t2, 314)
#fslice_value = 0
#fslice_value = 256
ICMP(t314,t286,'ICMP_ULE')
#fslice_value = 1
t315=A("add",t314,t2, 315)
#fslice_value = 0
#fslice_value = 256
ICMP(t315,t286,'ICMP_ULE')
#fslice_value = 1
t316=A("add",t315,t2, 316)
#fslice_value = 0
#fslice_value = 256
ICMP(t316,t286,'ICMP_ULE')
#fslice_value = 1
t317=A("add",t316,t2, 317)
#fslice_value = 0
#fslice_value = 256
ICMP(t317,t286,'ICMP_ULE')
#fslice_value = 1
t318=A("add",t317,t2, 318)
#fslice_value = 0
#fslice_value = 256
ICMP(t318,t286,'ICMP_ULE')
#fslice_value = 1
t319=A("add",t318,t2, 319)
#fslice_value = 0
#fslice_value = 256
ICMP(t319,t286,'ICMP_ULE')
#fslice_value = 1
t320=A("add",t319,t2, 320)
#fslice_value = 0
#fslice_value = 256
ICMP(t320,t286,'ICMP_ULE')
#fslice_value = 1
t321=A("add",t320,t2, 321)
#fslice_value = 0
#fslice_value = 256
ICMP(t321,t286,'ICMP_ULE')
#fslice_value = 1
t322=A("add",t321,t2, 322)
#fslice_value = 0
#fslice_value = 256
ICMP(t322,t286,'ICMP_ULE')
#fslice_value = 1
t323=A("add",t322,t2, 323)
#fslice_value = 0
#fslice_value = 256
ICMP(t323,t286,'ICMP_ULE')
#fslice_value = 1
t324=A("add",t323,t2, 324)
#fslice_value = 0
#fslice_value = 256
ICMP(t324,t286,'ICMP_ULE')
#fslice_value = 1
t325=A("add",t324,t2, 325)
#fslice_value = 0
#fslice_value = 256
ICMP(t325,t286,'ICMP_ULE')
#fslice_value = 1
t326=A("add",t325,t2, 326)
#fslice_value = 0
#fslice_value = 256
ICMP(t326,t286,'ICMP_ULE')
#fslice_value = 1
t327=A("add",t326,t2, 327)
#fslice_value = 0
#fslice_value = 256
ICMP(t327,t286,'ICMP_ULE')
#fslice_value = 1
t328=A("add",t327,t2, 328)
#fslice_value = 0
#fslice_value = 256
ICMP(t328,t286,'ICMP_ULE')
#fslice_value = 1
t329=A("add",t328,t2, 329)
#fslice_value = 0
#fslice_value = 256
ICMP(t329,t286,'ICMP_ULE')
#fslice_value = 1
t330=A("add",t329,t2, 330)
#fslice_value = 0
#fslice_value = 256
ICMP(t330,t286,'ICMP_ULE')
#fslice_value = 1
t331=A("add",t330,t2, 331)
#fslice_value = 0
#fslice_value = 256
ICMP(t331,t286,'ICMP_ULE')
#fslice_value = 1
t332=A("add",t331,t2, 332)
#fslice_value = 0
#fslice_value = 256
ICMP(t332,t286,'ICMP_ULE')
#fslice_value = 1
t333=A("add",t332,t2, 333)
#fslice_value = 0
#fslice_value = 256
ICMP(t333,t286,'ICMP_ULE')
#fslice_value = 1
t334=A("add",t333,t2, 334)
#fslice_value = 0
#fslice_value = 256
ICMP(t334,t286,'ICMP_ULE')
#fslice_value = 1
t335=A("add",t334,t2, 335)
#fslice_value = 0
#fslice_value = 256
ICMP(t335,t286,'ICMP_ULE')
#fslice_value = 1
t336=A("add",t335,t2, 336)
#fslice_value = 0
#fslice_value = 256
ICMP(t336,t286,'ICMP_ULE')
#fslice_value = 1
t337=A("add",t336,t2, 337)
#fslice_value = 0
#fslice_value = 256
ICMP(t337,t286,'ICMP_ULE')
#fslice_value = 1
t338=A("add",t337,t2, 338)
#fslice_value = 0
#fslice_value = 256
ICMP(t338,t286,'ICMP_ULE')
#fslice_value = 1
t339=A("add",t338,t2, 339)
#fslice_value = 0
#fslice_value = 256
ICMP(t339,t286,'ICMP_ULE')
#fslice_value = 1
t340=A("add",t339,t2, 340)
#fslice_value = 0
#fslice_value = 256
ICMP(t340,t286,'ICMP_ULE')
#fslice_value = 1
t341=A("add",t340,t2, 341)
#fslice_value = 0
#fslice_value = 256
ICMP(t341,t286,'ICMP_ULE')
#fslice_value = 1
t342=A("add",t341,t2, 342)
#fslice_value = 0
#fslice_value = 256
ICMP(t342,t286,'ICMP_ULE')
#fslice_value = 1
t343=A("add",t342,t2, 343)
#fslice_value = 0
#fslice_value = 256
ICMP(t343,t286,'ICMP_ULE')
#fslice_value = 1
t344=A("add",t343,t2, 344)
#fslice_value = 0
#fslice_value = 256
ICMP(t344,t286,'ICMP_ULE')
#fslice_value = 1
t345=A("add",t344,t2, 345)
#fslice_value = 0
#fslice_value = 256
ICMP(t345,t286,'ICMP_ULE')
#fslice_value = 1
t346=A("add",t345,t2, 346)
#fslice_value = 0
#fslice_value = 256
ICMP(t346,t286,'ICMP_ULE')
#fslice_value = 1
t347=A("add",t346,t2, 347)
#fslice_value = 0
#fslice_value = 256
ICMP(t347,t286,'ICMP_ULE')
#fslice_value = 1
t348=A("add",t347,t2, 348)
#fslice_value = 0
#fslice_value = 256
ICMP(t348,t286,'ICMP_ULE')
#fslice_value = 1
t349=A("add",t348,t2, 349)
#fslice_value = 0
#fslice_value = 256
ICMP(t349,t286,'ICMP_ULE')
#fslice_value = 1
t350=A("add",t349,t2, 350)
#fslice_value = 0
#fslice_value = 256
ICMP(t350,t286,'ICMP_ULE')
#fslice_value = 1
t351=A("add",t350,t2, 351)
#fslice_value = 0
#fslice_value = 256
ICMP(t351,t286,'ICMP_ULE')
#fslice_value = 1
t352=A("add",t351,t2, 352)
#fslice_value = 0
#fslice_value = 256
ICMP(t352,t286,'ICMP_ULE')
#fslice_value = 1
t353=A("add",t352,t2, 353)
#fslice_value = 0
#fslice_value = 256
ICMP(t353,t286,'ICMP_ULE')
#fslice_value = 1
t354=A("add",t353,t2, 354)
#fslice_value = 0
#fslice_value = 256
ICMP(t354,t286,'ICMP_ULE')
#fslice_value = 1
t355=A("add",t354,t2, 355)
#fslice_value = 0
#fslice_value = 256
ICMP(t355,t286,'ICMP_ULE')
#fslice_value = 1
t356=A("add",t355,t2, 356)
#fslice_value = 0
#fslice_value = 256
ICMP(t356,t286,'ICMP_ULE')
#fslice_value = 1
t357=A("add",t356,t2, 357)
#fslice_value = 0
#fslice_value = 256
ICMP(t357,t286,'ICMP_ULE')
#fslice_value = 1
t358=A("add",t357,t2, 358)
#fslice_value = 0
#fslice_value = 256
ICMP(t358,t286,'ICMP_ULE')
#fslice_value = 1
t359=A("add",t358,t2, 359)
#fslice_value = 0
#fslice_value = 256
ICMP(t359,t286,'ICMP_ULE')
#fslice_value = 1
t360=A("add",t359,t2, 360)
#fslice_value = 0
#fslice_value = 256
ICMP(t360,t286,'ICMP_ULE')
#fslice_value = 1
t361=A("add",t360,t2, 361)
#fslice_value = 0
#fslice_value = 256
ICMP(t361,t286,'ICMP_ULE')
#fslice_value = 1
t362=A("add",t361,t2, 362)
#fslice_value = 0
#fslice_value = 256
ICMP(t362,t286,'ICMP_ULE')
#fslice_value = 1
t363=A("add",t362,t2, 363)
#fslice_value = 0
#fslice_value = 256
ICMP(t363,t286,'ICMP_ULE')
#fslice_value = 1
t364=A("add",t363,t2, 364)
#fslice_value = 0
#fslice_value = 256
ICMP(t364,t286,'ICMP_ULE')
#fslice_value = 1
t365=A("add",t364,t2, 365)
#fslice_value = 0
#fslice_value = 256
ICMP(t365,t286,'ICMP_ULE')
#fslice_value = 1
t366=A("add",t365,t2, 366)
#fslice_value = 0
#fslice_value = 256
ICMP(t366,t286,'ICMP_ULE')
#fslice_value = 1
t367=A("add",t366,t2, 367)
#fslice_value = 0
#fslice_value = 256
ICMP(t367,t286,'ICMP_ULE')
#fslice_value = 1
t368=A("add",t367,t2, 368)
#fslice_value = 0
#fslice_value = 256
ICMP(t368,t286,'ICMP_ULE')
#fslice_value = 1
t369=A("add",t368,t2, 369)
#fslice_value = 0
#fslice_value = 256
ICMP(t369,t286,'ICMP_ULE')
#fslice_value = 1
t370=A("add",t369,t2, 370)
#fslice_value = 0
#fslice_value = 256
ICMP(t370,t286,'ICMP_ULE')
#fslice_value = 1
t371=A("add",t370,t2, 371)
#fslice_value = 0
#fslice_value = 256
ICMP(t371,t286,'ICMP_ULE')
#fslice_value = 1
t372=A("add",t371,t2, 372)
#fslice_value = 0
#fslice_value = 256
ICMP(t372,t286,'ICMP_ULE')
#fslice_value = 1
t373=A("add",t372,t2, 373)
#fslice_value = 0
#fslice_value = 256
ICMP(t373,t286,'ICMP_ULE')
#fslice_value = 1
t374=A("add",t373,t2, 374)
#fslice_value = 0
#fslice_value = 256
ICMP(t374,t286,'ICMP_ULE')
#fslice_value = 1
t375=A("add",t374,t2, 375)
#fslice_value = 0
#fslice_value = 256
ICMP(t375,t286,'ICMP_ULE')
#fslice_value = 1
t376=A("add",t375,t2, 376)
#fslice_value = 0
#fslice_value = 256
ICMP(t376,t286,'ICMP_ULE')
#fslice_value = 1
t377=A("add",t376,t2, 377)
#fslice_value = 0
#fslice_value = 256
ICMP(t377,t286,'ICMP_ULE')
#fslice_value = 1
t378=A("add",t377,t2, 378)
#fslice_value = 0
#fslice_value = 256
ICMP(t378,t286,'ICMP_ULE')
#fslice_value = 1
t379=A("add",t378,t2, 379)
#fslice_value = 0
#fslice_value = 256
ICMP(t379,t286,'ICMP_ULE')
#fslice_value = 1
t380=A("add",t379,t2, 380)
#fslice_value = 0
#fslice_value = 256
ICMP(t380,t286,'ICMP_ULE')
#fslice_value = 1
t381=A("add",t380,t2, 381)
#fslice_value = 0
#fslice_value = 256
ICMP(t381,t286,'ICMP_ULE')
#fslice_value = 1
t382=A("add",t381,t2, 382)
#fslice_value = 0
#fslice_value = 256
ICMP(t382,t286,'ICMP_ULE')
#fslice_value = 1
t383=A("add",t382,t2, 383)
#fslice_value = 0
#fslice_value = 256
ICMP(t383,t286,'ICMP_ULE')
#fslice_value = 1
t384=A("add",t383,t2, 384)
#fslice_value = 0
#fslice_value = 256
ICMP(t384,t286,'ICMP_ULE')
#fslice_value = 1
t385=A("add",t384,t2, 385)
#fslice_value = 0
#fslice_value = 256
ICMP(t385,t286,'ICMP_ULE')
#fslice_value = 1
t386=A("add",t385,t2, 386)
#fslice_value = 0
#fslice_value = 256
ICMP(t386,t286,'ICMP_ULE')
#fslice_value = 1
t387=A("add",t386,t2, 387)
#fslice_value = 0
#fslice_value = 256
ICMP(t387,t286,'ICMP_ULE')
#fslice_value = 1
t388=A("add",t387,t2, 388)
#fslice_value = 0
#fslice_value = 256
ICMP(t388,t286,'ICMP_ULE')
#fslice_value = 1
t389=A("add",t388,t2, 389)
#fslice_value = 0
#fslice_value = 256
ICMP(t389,t286,'ICMP_ULE')
#fslice_value = 1
t390=A("add",t389,t2, 390)
#fslice_value = 0
#fslice_value = 256
ICMP(t390,t286,'ICMP_ULE')
#fslice_value = 1
t391=A("add",t390,t2, 391)
#fslice_value = 0
#fslice_value = 256
ICMP(t391,t286,'ICMP_ULE')
#fslice_value = 1
t392=A("add",t391,t2, 392)
#fslice_value = 0
#fslice_value = 256
ICMP(t392,t286,'ICMP_ULE')
#fslice_value = 1
t393=A("add",t392,t2, 393)
#fslice_value = 0
#fslice_value = 256
ICMP(t393,t286,'ICMP_ULE')
#fslice_value = 1
t394=A("add",t393,t2, 394)
#fslice_value = 0
#fslice_value = 256
ICMP(t394,t286,'ICMP_ULE')
#fslice_value = 1
t395=A("add",t394,t2, 395)
#fslice_value = 0
#fslice_value = 256
ICMP(t395,t286,'ICMP_ULE')
#fslice_value = 1
t396=A("add",t395,t2, 396)
#fslice_value = 0
#fslice_value = 256
ICMP(t396,t286,'ICMP_ULE')
#fslice_value = 1
t397=A("add",t396,t2, 397)
#fslice_value = 0
#fslice_value = 256
ICMP(t397,t286,'ICMP_ULE')
#fslice_value = 1
t398=A("add",t397,t2, 398)
#fslice_value = 0
#fslice_value = 256
ICMP(t398,t286,'ICMP_ULE')
#fslice_value = 1
t399=A("add",t398,t2, 399)
#fslice_value = 0
#fslice_value = 256
ICMP(t399,t286,'ICMP_ULE')
#fslice_value = 1
t400=A("add",t399,t2, 400)
#fslice_value = 0
#fslice_value = 256
ICMP(t400,t286,'ICMP_ULE')
#fslice_value = 1
t401=A("add",t400,t2, 401)
#fslice_value = 0
#fslice_value = 256
ICMP(t401,t286,'ICMP_ULE')
#fslice_value = 1
t402=A("add",t401,t2, 402)
#fslice_value = 0
#fslice_value = 256
ICMP(t402,t286,'ICMP_ULE')
#fslice_value = 1
t403=A("add",t402,t2, 403)
#fslice_value = 0
#fslice_value = 256
ICMP(t403,t286,'ICMP_ULE')
#fslice_value = 1
t404=A("add",t403,t2, 404)
#fslice_value = 0
#fslice_value = 256
ICMP(t404,t286,'ICMP_ULE')
#fslice_value = 1
t405=A("add",t404,t2, 405)
#fslice_value = 0
#fslice_value = 256
ICMP(t405,t286,'ICMP_ULE')
#fslice_value = 1
t406=A("add",t405,t2, 406)
#fslice_value = 0
#fslice_value = 256
ICMP(t406,t286,'ICMP_ULE')
#fslice_value = 1
t407=A("add",t406,t2, 407)
#fslice_value = 0
#fslice_value = 256
ICMP(t407,t286,'ICMP_ULE')
#fslice_value = 1
t408=A("add",t407,t2, 408)
#fslice_value = 0
#fslice_value = 256
ICMP(t408,t286,'ICMP_ULE')
#fslice_value = 1
t409=A("add",t408,t2, 409)
#fslice_value = 0
#fslice_value = 256
ICMP(t409,t286,'ICMP_ULE')
#fslice_value = 1
t410=A("add",t409,t2, 410)
#fslice_value = 0
#fslice_value = 256
ICMP(t410,t286,'ICMP_ULE')
#fslice_value = 1
t411=A("add",t410,t2, 411)
#fslice_value = 0
#fslice_value = 256
ICMP(t411,t286,'ICMP_ULE')
#fslice_value = 1
t412=A("add",t411,t2, 412)
#fslice_value = 0
#fslice_value = 256
ICMP(t412,t286,'ICMP_ULE')
#fslice_value = 1
t413=A("add",t412,t2, 413)
#fslice_value = 0
#fslice_value = 256
ICMP(t413,t286,'ICMP_ULE')
#fslice_value = 1
t414=A("add",t413,t2, 414)
#fslice_value = 0
#fslice_value = 256
ICMP(t414,t286,'ICMP_ULE')
#fslice_value = 1
t415=A("add",t414,t2, 415)
#fslice_value = 0
#fslice_value = 256
ICMP(t415,t286,'ICMP_ULE')
#fslice_value = 1
t416=A("add",t415,t2, 416)
#fslice_value = 0
#fslice_value = 256
ICMP(t416,t286,'ICMP_ULE')
#fslice_value = 1
t417=A("add",t416,t2, 417)
#fslice_value = 0
#fslice_value = 256
ICMP(t417,t286,'ICMP_ULE')
#fslice_value = 1
t418=A("add",t417,t2, 418)
#fslice_value = 0
#fslice_value = 256
ICMP(t418,t286,'ICMP_ULE')
#fslice_value = 1
t419=A("add",t418,t2, 419)
#fslice_value = 0
#fslice_value = 256
ICMP(t419,t286,'ICMP_ULE')
#fslice_value = 1
t420=A("add",t419,t2, 420)
#fslice_value = 0
#fslice_value = 256
ICMP(t420,t286,'ICMP_ULE')
#fslice_value = 1
t421=A("add",t420,t2, 421)
#fslice_value = 0
#fslice_value = 256
ICMP(t421,t286,'ICMP_ULE')
#fslice_value = 1
t422=A("add",t421,t2, 422)
#fslice_value = 0
#fslice_value = 256
ICMP(t422,t286,'ICMP_ULE')
#fslice_value = 1
t423=A("add",t422,t2, 423)
#fslice_value = 0
#fslice_value = 256
ICMP(t423,t286,'ICMP_ULE')
#fslice_value = 1
t424=A("add",t423,t2, 424)
#fslice_value = 0
#fslice_value = 256
ICMP(t424,t286,'ICMP_ULE')
#fslice_value = 1
t425=A("add",t424,t2, 425)
#fslice_value = 0
#fslice_value = 256
ICMP(t425,t286,'ICMP_ULE')
#fslice_value = 1
t426=A("add",t425,t2, 426)
#fslice_value = 0
#fslice_value = 256
ICMP(t426,t286,'ICMP_ULE')
#fslice_value = 1
t427=A("add",t426,t2, 427)
#fslice_value = 0
#fslice_value = 256
ICMP(t427,t286,'ICMP_ULE')
#fslice_value = 1
t428=A("add",t427,t2, 428)
#fslice_value = 0
#fslice_value = 256
ICMP(t428,t286,'ICMP_ULE')
#fslice_value = 1
t429=A("add",t428,t2, 429)
#fslice_value = 0
#fslice_value = 256
ICMP(t429,t286,'ICMP_ULE')
#fslice_value = 1
t430=A("add",t429,t2, 430)
#fslice_value = 0
#fslice_value = 256
ICMP(t430,t286,'ICMP_ULE')
#fslice_value = 1
t431=A("add",t430,t2, 431)
#fslice_value = 0
#fslice_value = 256
ICMP(t431,t286,'ICMP_ULE')
#fslice_value = 1
t432=A("add",t431,t2, 432)
#fslice_value = 0
#fslice_value = 256
ICMP(t432,t286,'ICMP_ULE')
#fslice_value = 1
t433=A("add",t432,t2, 433)
#fslice_value = 0
#fslice_value = 256
ICMP(t433,t286,'ICMP_ULE')
#fslice_value = 1
t434=A("add",t433,t2, 434)
#fslice_value = 0
#fslice_value = 256
ICMP(t434,t286,'ICMP_ULE')
#fslice_value = 1
t435=A("add",t434,t2, 435)
#fslice_value = 0
#fslice_value = 256
ICMP(t435,t286,'ICMP_ULE')
#fslice_value = 1
t436=A("add",t435,t2, 436)
#fslice_value = 0
#fslice_value = 256
ICMP(t436,t286,'ICMP_ULE')
#fslice_value = 1
t437=A("add",t436,t2, 437)
#fslice_value = 0
#fslice_value = 256
ICMP(t437,t286,'ICMP_ULE')
#fslice_value = 1
t438=A("add",t437,t2, 438)
#fslice_value = 0
#fslice_value = 256
ICMP(t438,t286,'ICMP_ULE')
#fslice_value = 1
t439=A("add",t438,t2, 439)
#fslice_value = 0
#fslice_value = 256
ICMP(t439,t286,'ICMP_ULE')
#fslice_value = 1
t440=A("add",t439,t2, 440)
#fslice_value = 0
#fslice_value = 256
ICMP(t440,t286,'ICMP_ULE')
#fslice_value = 1
t441=A("add",t440,t2, 441)
#fslice_value = 0
#fslice_value = 256
ICMP(t441,t286,'ICMP_ULE')
#fslice_value = 1
t442=A("add",t441,t2, 442)
#fslice_value = 0
#fslice_value = 256
ICMP(t442,t286,'ICMP_ULE')
#fslice_value = 1
t443=A("add",t442,t2, 443)
#fslice_value = 0
#fslice_value = 256
ICMP(t443,t286,'ICMP_ULE')
#fslice_value = 1
t444=A("add",t443,t2, 444)
#fslice_value = 0
#fslice_value = 256
ICMP(t444,t286,'ICMP_ULE')
#fslice_value = 1
t445=A("add",t444,t2, 445)
#fslice_value = 0
#fslice_value = 256
ICMP(t445,t286,'ICMP_ULE')
#fslice_value = 1
t446=A("add",t445,t2, 446)
#fslice_value = 0
#fslice_value = 256
ICMP(t446,t286,'ICMP_ULE')
#fslice_value = 1
t447=A("add",t446,t2, 447)
#fslice_value = 0
#fslice_value = 256
ICMP(t447,t286,'ICMP_ULE')
#fslice_value = 1
t448=A("add",t447,t2, 448)
#fslice_value = 0
#fslice_value = 256
ICMP(t448,t286,'ICMP_ULE')
#fslice_value = 1
t449=A("add",t448,t2, 449)
#fslice_value = 0
#fslice_value = 256
ICMP(t449,t286,'ICMP_ULE')
#fslice_value = 1
t450=A("add",t449,t2, 450)
#fslice_value = 0
#fslice_value = 256
ICMP(t450,t286,'ICMP_ULE')
#fslice_value = 1
t451=A("add",t450,t2, 451)
#fslice_value = 0
#fslice_value = 256
ICMP(t451,t286,'ICMP_ULE')
#fslice_value = 1
t452=A("add",t451,t2, 452)
#fslice_value = 0
#fslice_value = 256
ICMP(t452,t286,'ICMP_ULE')
#fslice_value = 1
t453=A("add",t452,t2, 453)
#fslice_value = 0
#fslice_value = 256
ICMP(t453,t286,'ICMP_ULE')
#fslice_value = 1
t454=A("add",t453,t2, 454)
#fslice_value = 0
#fslice_value = 256
ICMP(t454,t286,'ICMP_ULE')
#fslice_value = 1
t455=A("add",t454,t2, 455)
#fslice_value = 0
#fslice_value = 256
ICMP(t455,t286,'ICMP_ULE')
#fslice_value = 1
t456=A("add",t455,t2, 456)
#fslice_value = 0
#fslice_value = 256
ICMP(t456,t286,'ICMP_ULE')
#fslice_value = 1
t457=A("add",t456,t2, 457)
#fslice_value = 0
#fslice_value = 256
ICMP(t457,t286,'ICMP_ULE')
#fslice_value = 1
t458=A("add",t457,t2, 458)
#fslice_value = 0
#fslice_value = 256
ICMP(t458,t286,'ICMP_ULE')
#fslice_value = 1
t459=A("add",t458,t2, 459)
#fslice_value = 0
#fslice_value = 256
ICMP(t459,t286,'ICMP_ULE')
#fslice_value = 1
t460=A("add",t459,t2, 460)
#fslice_value = 0
#fslice_value = 256
ICMP(t460,t286,'ICMP_ULE')
#fslice_value = 1
t461=A("add",t460,t2, 461)
#fslice_value = 0
#fslice_value = 256
ICMP(t461,t286,'ICMP_ULE')
#fslice_value = 1
t462=A("add",t461,t2, 462)
#fslice_value = 0
#fslice_value = 256
ICMP(t462,t286,'ICMP_ULE')
#fslice_value = 1
t463=A("add",t462,t2, 463)
#fslice_value = 0
#fslice_value = 256
ICMP(t463,t286,'ICMP_ULE')
#fslice_value = 1
t464=A("add",t463,t2, 464)
#fslice_value = 0
#fslice_value = 256
ICMP(t464,t286,'ICMP_ULE')
#fslice_value = 1
t465=A("add",t464,t2, 465)
#fslice_value = 0
#fslice_value = 256
ICMP(t465,t286,'ICMP_ULE')
#fslice_value = 1
t466=A("add",t465,t2, 466)
#fslice_value = 0
#fslice_value = 256
ICMP(t466,t286,'ICMP_ULE')
#fslice_value = 1
t467=A("add",t466,t2, 467)
#fslice_value = 0
#fslice_value = 256
ICMP(t467,t286,'ICMP_ULE')
#fslice_value = 1
t468=A("add",t467,t2, 468)
#fslice_value = 0
#fslice_value = 256
ICMP(t468,t286,'ICMP_ULE')
#fslice_value = 1
t469=A("add",t468,t2, 469)
#fslice_value = 0
#fslice_value = 256
ICMP(t469,t286,'ICMP_ULE')
#fslice_value = 1
t470=A("add",t469,t2, 470)
#fslice_value = 0
#fslice_value = 256
ICMP(t470,t286,'ICMP_ULE')
#fslice_value = 1
t471=A("add",t470,t2, 471)
#fslice_value = 0
#fslice_value = 256
ICMP(t471,t286,'ICMP_ULE')
#fslice_value = 1
t472=A("add",t471,t2, 472)
#fslice_value = 0
#fslice_value = 256
ICMP(t472,t286,'ICMP_ULE')
#fslice_value = 1
t473=A("add",t472,t2, 473)
#fslice_value = 0
#fslice_value = 256
ICMP(t473,t286,'ICMP_ULE')
#fslice_value = 1
t474=A("add",t473,t2, 474)
#fslice_value = 0
#fslice_value = 256
ICMP(t474,t286,'ICMP_ULE')
#fslice_value = 1
t475=A("add",t474,t2, 475)
#fslice_value = 0
#fslice_value = 256
ICMP(t475,t286,'ICMP_ULE')
#fslice_value = 1
t476=A("add",t475,t2, 476)
#fslice_value = 0
#fslice_value = 256
ICMP(t476,t286,'ICMP_ULE')
#fslice_value = 1
t477=A("add",t476,t2, 477)
#fslice_value = 0
#fslice_value = 256
ICMP(t477,t286,'ICMP_ULE')
#fslice_value = 1
t478=A("add",t477,t2, 478)
#fslice_value = 0
#fslice_value = 256
ICMP(t478,t286,'ICMP_ULE')
#fslice_value = 1
t479=A("add",t478,t2, 479)
#fslice_value = 0
#fslice_value = 256
ICMP(t479,t286,'ICMP_ULE')
#fslice_value = 1
t480=A("add",t479,t2, 480)
#fslice_value = 0
#fslice_value = 256
ICMP(t480,t286,'ICMP_ULE')
#fslice_value = 1
t481=A("add",t480,t2, 481)
#fslice_value = 0
#fslice_value = 256
ICMP(t481,t286,'ICMP_ULE')
#fslice_value = 1
t482=A("add",t481,t2, 482)
#fslice_value = 0
#fslice_value = 256
ICMP(t482,t286,'ICMP_ULE')
# SSSS Returning back from functioninode_hash_init
#fslice_value = 0
# SSSS Returning back from functiontestfs_init_super_block
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_UGT')
#fslice_value = 0
# testfs_get_inode()
# SSSS Calling function testfs_get_inode
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
# inode_hash_find()
# SSSS Calling function inode_hash_find
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 8
# hash_int()
# SSSS Calling function hash_int
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2654404609
t483=V(2654404609, 483) # Taint<483, 0, 0>
t484=A("mul",t1,t483, 484)
#fslice_value = 0
#fslice_value = 32
t485=V(32, 485) # Taint<485, 0, 0>
t486=A("sub",t485,t15, 486)
t487=A("lshr",t484,t486, 487)
# SSSS Returning back from functionhash_int
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
# SSSS Returning back from functioninode_hash_find
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 72
t488=M(72, 0, 488,t2,t4)
#fslice_value = 0
ICMP(t0,t0,'ICMP_EQ')
#fslice_value = 0
#fslice_value = 1
# testfs_read_inode_block()
# SSSS Calling function testfs_read_inode_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
# testfs_inode_to_block_nr()
# SSSS Calling function testfs_inode_to_block_nr
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2
t489=A("udiv",t1,t35, 489)
#fslice_value = 0
#fslice_value = 0
ICMP(t489,t1,'ICMP_ULT')
#fslice_value = 128
t490=V(128, 490) # Taint<490, 0, 0>
ICMP(t489,t490,'ICMP_ULE')
# SSSS Returning back from functiontestfs_inode_to_block_nr
#fslice_value = 0
 #YYY assigned new taint id = 10 taint id checked for = 10
t491=O(t10,491,t10[12],t10[13],t10[14],t10[15]) # Load(32700652, 4)
t492=A("add",t491,t489, 492)#SWITCH 491 0
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 4:read_blocks()--->testfs_read_inode_block()--->testfs_get_inode()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t493=A("mul",t492,t7, 493)
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
t494=A("add",t492,t1, 494)
#fslice_value = 64
#gBlockTAINT 495
t495=B(64,64,t7,t494, 495) # GetBlock(64, 64) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_read_inode_block
# testfs_inode_to_block_offset()
# SSSS Calling function testfs_inode_to_block_offset
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2
t496=A("urem",t1,t35, 496)
#fslice_value = 32
t497=A("mul",t496,t485, 497)
#fslice_value = 0
#fslice_value = 0
ICMP(t497,t1,'ICMP_ULT')
#fslice_value = 64
ICMP(t497,t7,'ICMP_ULE')
# SSSS Returning back from functiontestfs_inode_to_block_offset
#fslice_value = 0
t488[4]=t495[0] # fslice_memmove
t488[5]=t495[1] # fslice_memmove
t488[6]=t495[2] # fslice_memmove
t488[7]=t495[3] # fslice_memmove
t488[8]=t495[4] # fslice_memmove
t488[9]=t495[5] # fslice_memmove
t488[10]=t495[6] # fslice_memmove
t488[11]=t495[7] # fslice_memmove
t488[12]=t495[8] # fslice_memmove
t488[13]=t495[9] # fslice_memmove
t488[14]=t495[10] # fslice_memmove
t488[15]=t495[11] # fslice_memmove
t488[16]=t495[12] # fslice_memmove
t488[17]=t495[13] # fslice_memmove
t488[18]=t495[14] # fslice_memmove
t488[19]=t495[15] # fslice_memmove
t488[20]=t495[16] # fslice_memmove
t488[21]=t495[17] # fslice_memmove
t488[22]=t495[18] # fslice_memmove
t488[23]=t495[19] # fslice_memmove
t488[24]=t495[20] # fslice_memmove
t488[25]=t495[21] # fslice_memmove
t488[26]=t495[22] # fslice_memmove
t488[27]=t495[23] # fslice_memmove
t488[28]=t495[24] # fslice_memmove
t488[29]=t495[25] # fslice_memmove
t488[30]=t495[26] # fslice_memmove
t488[31]=t495[27] # fslice_memmove
t488[32]=t495[28] # fslice_memmove
t488[33]=t495[29] # fslice_memmove
t488[34]=t495[30] # fslice_memmove
t488[35]=t495[31] # fslice_memmove
#DSTRUCT:t495,0:Size|32
#testfs_get_inode:&in->in
#testfs_get_inode:block + block_offset
# inode_hash_insert()
# SSSS Calling function inode_hash_insert
#fslice_value = 0
#fslice_value = 0
# INIT_HLIST_NODE()
# SSSS Calling function INIT_HLIST_NODE
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functionINIT_HLIST_NODE
#fslice_value = 8
# hash_int()
# SSSS Calling function hash_int
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2654404609
#fslice_value = 0
#fslice_value = 32
# SSSS Returning back from functionhash_int
# hlist_add_head()
# SSSS Calling function hlist_add_head
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# SSSS Returning back from functionhlist_add_head
# SSSS Returning back from functioninode_hash_insert
# SSSS Returning back from functiontestfs_get_inode
#fslice_value = 0
#fslice_value = 18446744073709551615
t498=V(18446744073709551615, 498) # Taint<498, 0, 0>
ICMP(t0,t498,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
# handle_command()
# SSSS Calling function handle_command
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_EQ')
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
ICMP(t11,t0,'ICMP_ULE')
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 0
ICMP(t42,t0,'ICMP_ULE')
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 5
t499=V(5, 499) # Taint<499, 0, 0>
ICMP(t55,t499,'ICMP_SGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 5
ICMP(t59,t499,'ICMP_SGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 5
ICMP(t63,t499,'ICMP_SGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 5
ICMP(t67,t499,'ICMP_SGT')
# cmd_mkdir()
# SSSS Calling function cmd_mkdir
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2
ICMP(t42,t35,'ICMP_UGT')
t500=SYMBOLIC_STR()
#fslice_value = 2
# testfs_create_file_or_dir()
# SSSS Calling function testfs_create_file_or_dir
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_UGT')
t501=STRLEN(t500)
#fslice_value = 1
t502=A("sub",t501,t2, 502)
#fslice_value = 0
#fslice_value = 0
ICMP(t502,t1,'ICMP_ULT')
#fslice_value = 47
t503=V(47, 503) # Taint<503, 0, 0>
ICMP(t0,t503,'ICMP_EQ')
#fslice_value = 4294967295
t504=V(4294967295, 504) # Taint<504, 0, 0>
t505=A("add",t502,t504, 505)
#fslice_value = 0
#fslice_value = 0
ICMP(t505,t1,'ICMP_ULT')
#fslice_value = 47
ICMP(t0,t503,'ICMP_EQ')
#fslice_value = 4294967295
t506=A("add",t505,t504, 506)
#fslice_value = 0
#fslice_value = 0
ICMP(t506,t1,'ICMP_ULT')
#fslice_value = 47
ICMP(t500,t503,'ICMP_EQ')
#fslice_value = 4294967295
t507=A("add",t506,t504, 507)
#fslice_value = 0
#fslice_value = 0
ICMP(t507,t1,'ICMP_ULT')
#fslice_value = 0
ICMP(t507,t1,'ICMP_ULT')
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
t508=STRLEN(t500)
#fslice_value = 1
t509=A("add",t508,t2, 509)
#fslice_value = 56
t510=V(56, 510) # Taint<510, 0, 0>
ICMP(t509,t510,'ICMP_UGE')
#fslice_value = 2
# testfs_tx_start()
# SSSS Calling function testfs_tx_start
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
# SSSS Returning back from functiontestfs_tx_start
ICMP(t0,t0,'ICMP_UGT')
# testfs_dir_name_to_inode_nr()
# SSSS Calling function testfs_dir_name_to_inode_nr
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
# testfs_inode_get_nr()
# SSSS Calling function testfs_inode_get_nr
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_nr
#fslice_value = 0
t511=STRLEN(t500)
#fslice_value = 1
t512=A("sub",t511,t2, 512)
#fslice_value = 47
ICMP(t0,t503,'ICMP_EQ')
# testfs_dir_name_to_inode_nr_rec()
# SSSS Calling function testfs_dir_name_to_inode_nr_rec
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
 #YYY assigned new taint id = 495 taint id checked for = 495
t513=O(t495,513,t495[0],t495[1],t495[2],t495[3]) # Load(33005140, 4)
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t513,t35,'ICMP_EQ')
#fslice_value = 0
ICMP(t0,t1,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
t514=STRLEN(t500)
ICMP(t1,t514,'ICMP_ULE')
#fslice_value = 47
ICMP(t500,t503,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
t515=STRLEN(t500)
ICMP(t11,t515,'ICMP_ULE')
#fslice_value = 47
ICMP(t0,t503,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
t516=STRLEN(t500)
ICMP(t42,t516,'ICMP_ULE')
#fslice_value = 47
ICMP(t0,t503,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
t517=STRLEN(t500)
ICMP(t55,t517,'ICMP_ULE')
#fslice_value = 4294967295
#fslice_value = 0
ICMP(t504,t1,'ICMP_EQ')
t518=STRLEN(t500)
#fslice_value = 1
t519=A("sub",t518,t2, 519)
ICMP(t504,t519,'ICMP_EQ')
#fslice_value = 4294967295
ICMP(t504,t504,'ICMP_UGT')
#fslice_value = 4294967294
t520=V(4294967294, 520) # Taint<520, 0, 0>
#fslice_value = 0
ICMP(t520,t1,'ICMP_ULE')
# testfs_next_dirent()
# SSSS Calling function testfs_next_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t513,t35,'ICMP_EQ')
# testfs_inode_get_size()
# SSSS Calling function testfs_inode_get_size
#fslice_value = 0
#fslice_value = 0
 #YYY assigned new taint id = 495 taint id checked for = 495
t521=O(t495,521,t495[4],t495[5],t495[6],t495[7]) # Load(33005144, 4)
# SSSS Returning back from functiontestfs_inode_get_size
ICMP(t1,t521,'ICMP_ULT')
#fslice_value = 8
t522=A("add",t1,t15, 522)
#fslice_value = 64
t523=A("udiv",t522,t7, 523)
#fslice_value = 64
t524=A("sdiv",t1,t7, 524)
ICMP(t523,t524,'ICMP_UGE')
#fslice_value = 8
# testfs_read_data()
# SSSS Calling function testfs_read_data
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 64
t525=A("srem",t1,t7, 525)
ICMP(t522,t521,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 64
t526=A("sdiv",t9,t7, 526)
#fslice_value = 0
# testfs_get_block()
# SSSS Calling function testfs_get_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t526,t1,'ICMP_ULT')
#fslice_value = 4
t527=V(4, 527) # Taint<527, 0, 0>
ICMP(t526,t527,'ICMP_ULE')
 #YYY assigned new taint id = 495 taint id checked for = 495
t528=O(t495,528,t495[12],t495[13],t495[14],t495[15]) # Load(33005152, 4)
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 10:read_blocks()--->testfs_get_block()--->testfs_read_data()--->testfs_next_dirent()--->testfs_dir_name_to_inode_nr_rec()--->testfs_dir_name_to_inode_nr()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t529=A("mul",t528,t7, 529)#SWITCH 528 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
t530=A("add",t528,t1, 530)#SWITCH 528 64
#fslice_value = 64
#gBlockTAINT 531
t531=B(64,192,t7,t530, 531) # GetBlock(64, 192) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_get_block
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
t532=A("sub",t15,t1, 532)
#fslice_value = 64
t533=A("sub",t7,t525, 533)
ICMP(t532,t533,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
#DSTRUCT:t531,0:Size|8
#testfs_read_data:buf + buf_offset
#testfs_read_data:block + b_offset
t534=A("add",t1,t532, 534)
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 1
t535=A("xor",t0,t2, 535)
#fslice_value = 0
# SSSS Returning back from functiontestfs_read_data
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
 #YYY assigned new taint id = 531 taint id checked for = 531
t536=O(t531,536,t531[0],t531[1],t531[2],t531[3]) # Load(140727937607136, 4)
#fslice_value = 0
ICMP(t536,t1,'ICMP_EQ')
#fslice_value = 8
t537=A("add",t15,t536, 537)
t538=M(10, 0, 538,t537)
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
t538[0]=t531[0] # fslice_memmove
t538[1]=t531[1] # fslice_memmove
t538[2]=t531[2] # fslice_memmove
t538[3]=t531[3] # fslice_memmove
t538[4]=t531[4] # fslice_memmove
t538[5]=t531[5] # fslice_memmove
t538[6]=t531[6] # fslice_memmove
t538[7]=t531[7] # fslice_memmove
#DSTRUCT:t531,0:Size|8
#fslice_value = 8
# testfs_read_data()
# SSSS Calling function testfs_read_data
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 64
t539=A("srem",t522,t7, 539)
t540=A("add",t522,t536, 540)
ICMP(t540,t521,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
t541=A("add",t522,t1, 541)
#fslice_value = 64
t542=A("sdiv",t541,t7, 542)
#fslice_value = 0
# testfs_get_block()
# SSSS Calling function testfs_get_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t542,t1,'ICMP_ULT')
#fslice_value = 4
ICMP(t542,t527,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 10:read_blocks()--->testfs_get_block()--->testfs_read_data()--->testfs_next_dirent()--->testfs_dir_name_to_inode_nr_rec()--->testfs_dir_name_to_inode_nr()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 543
t543=B(64,192,t7,t530, 543) # GetBlock(64, 192) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_get_block
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
t544=A("sub",t536,t1, 544)#SWITCH 536 192
#fslice_value = 64
t545=A("sub",t7,t539, 545)
ICMP(t544,t545,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t538[8]=t543[8] # fslice_memmove
t538[9]=t543[9] # fslice_memmove
#DSTRUCT:t543,8:Size|2
#testfs_read_data:buf + buf_offset
#testfs_read_data:block + b_offset
t546=A("add",t1,t544, 546)
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
# SSSS Returning back from functiontestfs_read_data
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# SSSS Returning back from functiontestfs_next_dirent
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
t547=O(t531,547,t531[4],t531[5],t531[6],t531[7]) # Load(33034676, 4)
#fslice_value = 0
ICMP(t547,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t0,t1,'ICMP_UGT')
#fslice_value = 0
ICMP(t520,t1,'ICMP_ULE')
# testfs_next_dirent()
# SSSS Calling function testfs_next_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t513,t35,'ICMP_EQ')
# testfs_inode_get_size()
# SSSS Calling function testfs_inode_get_size
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_size
ICMP(t540,t521,'ICMP_ULT')
#fslice_value = 8
t548=A("add",t540,t15, 548)
#fslice_value = 64
t549=A("udiv",t548,t7, 549)
#fslice_value = 64
t550=A("sdiv",t540,t7, 550)
ICMP(t549,t550,'ICMP_UGE')
#fslice_value = 8
# testfs_read_data()
# SSSS Calling function testfs_read_data
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 64
t551=A("srem",t540,t7, 551)
ICMP(t548,t521,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
t552=A("add",t540,t1, 552)
#fslice_value = 64
t553=A("sdiv",t552,t7, 553)
#fslice_value = 0
# testfs_get_block()
# SSSS Calling function testfs_get_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t553,t1,'ICMP_ULT')
#fslice_value = 4
ICMP(t553,t527,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 10:read_blocks()--->testfs_get_block()--->testfs_read_data()--->testfs_next_dirent()--->testfs_dir_name_to_inode_nr_rec()--->testfs_dir_name_to_inode_nr()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 554
t554=B(64,192,t7,t530, 554) # GetBlock(64, 192) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_get_block
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
#fslice_value = 64
t555=A("sub",t7,t551, 555)
ICMP(t532,t555,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t531[0]=t554[10] # fslice_memmove
t531[1]=t554[11] # fslice_memmove
t531[2]=t554[12] # fslice_memmove
t531[3]=t554[13] # fslice_memmove
t531[4]=t554[14] # fslice_memmove
t531[5]=t554[15] # fslice_memmove
t531[6]=t554[16] # fslice_memmove
t531[7]=t554[17] # fslice_memmove
#DSTRUCT:t554,10:Size|8
#testfs_read_data:buf + buf_offset
#testfs_read_data:block + b_offset
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
# SSSS Returning back from functiontestfs_read_data
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
 #YYY assigned new taint id = 554 taint id checked for = 554
t556=O(t554,556,t554[10],t554[11],t554[12],t554[13]) # Load(140727937607136, 4)
#fslice_value = 0
ICMP(t556,t1,'ICMP_EQ')
#fslice_value = 8
t557=A("add",t15,t556, 557)
t558=M(11, 0, 558,t557)
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
t558[0]=t554[10] # fslice_memmove
t558[1]=t554[11] # fslice_memmove
t558[2]=t554[12] # fslice_memmove
t558[3]=t554[13] # fslice_memmove
t558[4]=t554[14] # fslice_memmove
t558[5]=t554[15] # fslice_memmove
t558[6]=t554[16] # fslice_memmove
t558[7]=t554[17] # fslice_memmove
#DSTRUCT:t554,10:Size|8
#fslice_value = 8
# testfs_read_data()
# SSSS Calling function testfs_read_data
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 64
t559=A("srem",t548,t7, 559)
t560=A("add",t548,t556, 560)
ICMP(t560,t521,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
t561=A("add",t548,t1, 561)
#fslice_value = 64
t562=A("sdiv",t561,t7, 562)
#fslice_value = 0
# testfs_get_block()
# SSSS Calling function testfs_get_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t562,t1,'ICMP_ULT')
#fslice_value = 4
ICMP(t562,t527,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 10:read_blocks()--->testfs_get_block()--->testfs_read_data()--->testfs_next_dirent()--->testfs_dir_name_to_inode_nr_rec()--->testfs_dir_name_to_inode_nr()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 563
t563=B(64,192,t7,t530, 563) # GetBlock(64, 192) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_get_block
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
t564=A("sub",t556,t1, 564)#SWITCH 556 192
#fslice_value = 64
t565=A("sub",t7,t559, 565)
ICMP(t564,t565,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t558[8]=t563[18] # fslice_memmove
t558[9]=t563[19] # fslice_memmove
t558[10]=t563[20] # fslice_memmove
#DSTRUCT:t563,18:Size|3
#testfs_read_data:buf + buf_offset
#testfs_read_data:block + b_offset
t566=A("add",t1,t564, 566)
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
# SSSS Returning back from functiontestfs_read_data
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# SSSS Returning back from functiontestfs_next_dirent
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
t567=O(t554,567,t554[14],t554[15],t554[16],t554[17]) # Load(33037828, 4)
#fslice_value = 0
ICMP(t567,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t0,t1,'ICMP_UGT')
#fslice_value = 0
ICMP(t520,t1,'ICMP_ULE')
# testfs_next_dirent()
# SSSS Calling function testfs_next_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t513,t35,'ICMP_EQ')
# testfs_inode_get_size()
# SSSS Calling function testfs_inode_get_size
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_size
ICMP(t560,t521,'ICMP_ULT')
# SSSS Returning back from functiontestfs_next_dirent
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 4294967295
ICMP(t504,t504,'ICMP_UGT')
# SSSS Returning back from functiontestfs_dir_name_to_inode_nr_rec
#fslice_value = 0
# testfs_inode_get_nr()
# SSSS Calling function testfs_inode_get_nr
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_nr
ICMP(t1,t1,'ICMP_UGT')
# SSSS Returning back from functiontestfs_dir_name_to_inode_nr
#fslice_value = 0
#fslice_value = 0
ICMP(t520,t1,'ICMP_ULT')
# testfs_create_inode()
# SSSS Calling function testfs_create_inode
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
# testfs_get_inode_freemap()
# SSSS Calling function testfs_get_inode_freemap
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# bitmap_alloc()
# SSSS Calling function bitmap_alloc
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 8
#fslice_value = 1
#fslice_value = 8
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t18,'ICMP_ULE')
 #YYY assigned new taint id = 25 taint id checked for = 25
t568=O(t25,568,t25[0]) # Load(32711568, 1)
#fslice_value = 255
t569=V(255, 569) # Taint<569, 0, 0>
ICMP(t568,t569,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 8
ICMP(t1,t15,'ICMP_ULE')
#fslice_value = 1
t570=A("shl",t2,t1, 570)
#fslice_value = 0
t571=A("and",t568,t570, 571)#SWITCH 568 1
#fslice_value = 0
ICMP(t571,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 8
ICMP(t11,t15,'ICMP_ULE')
#fslice_value = 1
t572=A("shl",t2,t11, 572)
#fslice_value = 0
t573=A("and",t568,t572, 573)#SWITCH 568 1
#fslice_value = 0
ICMP(t573,t1,'ICMP_EQ')
t574=A("or",t568,t572, 574)#SWITCH 568 1
#fslice_value = 8
t575=A("mul",t1,t15, 575)
t576=A("add",t575,t11, 576)
ICMP(t576,t12,'ICMP_ULE')
#fslice_value = 0
# SSSS Returning back from functionbitmap_alloc
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# testfs_write_inode_freemap()
# SSSS Calling function testfs_write_inode_freemap
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# bitmap_getdata()
# SSSS Calling function bitmap_getdata
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functionbitmap_getdata
#fslice_value = 0
#fslice_value = 512
t577=A("sdiv",t576,t12, 577)
#fslice_value = 0
#fslice_value = 64
t578=A("mul",t577,t7, 578)
t579=A("add",t22,t577, 579)#SWITCH 22 0
#fslice_value = 1
# write_blocks()
# SSSS Calling function write_blocks
# SSSS CALL STACK 8:write_blocks()--->testfs_write_inode_freemap()--->testfs_get_inode_freemap()--->testfs_create_inode()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t580=A("mul",t579,t7, 580)
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
t581=A("add",t579,t1, 581)
#fslice_value = 64
#gBlockTAINT 582
t582=B(64,1,t7,t581, 582) # GetBlock(64, 1) w
t582[0]=t574[0] # fslice_write_block(32711568, 64, 1)
t582[1]=t25[1] # fslice_write_block(32711568, 64, 1)
t582[2]=t25[2] # fslice_write_block(32711568, 64, 1)
t582[3]=t25[3] # fslice_write_block(32711568, 64, 1)
t582[4]=t25[4] # fslice_write_block(32711568, 64, 1)
t582[5]=t25[5] # fslice_write_block(32711568, 64, 1)
t582[6]=t25[6] # fslice_write_block(32711568, 64, 1)
t582[7]=t25[7] # fslice_write_block(32711568, 64, 1)
t582[8]=t25[8] # fslice_write_block(32711568, 64, 1)
t582[9]=t25[9] # fslice_write_block(32711568, 64, 1)
t582[10]=t25[10] # fslice_write_block(32711568, 64, 1)
t582[11]=t25[11] # fslice_write_block(32711568, 64, 1)
t582[12]=t25[12] # fslice_write_block(32711568, 64, 1)
t582[13]=t25[13] # fslice_write_block(32711568, 64, 1)
t582[14]=t25[14] # fslice_write_block(32711568, 64, 1)
t582[15]=t25[15] # fslice_write_block(32711568, 64, 1)
t582[16]=t25[16] # fslice_write_block(32711568, 64, 1)
t582[17]=t25[17] # fslice_write_block(32711568, 64, 1)
t582[18]=t25[18] # fslice_write_block(32711568, 64, 1)
t582[19]=t25[19] # fslice_write_block(32711568, 64, 1)
t582[20]=t25[20] # fslice_write_block(32711568, 64, 1)
t582[21]=t25[21] # fslice_write_block(32711568, 64, 1)
t582[22]=t25[22] # fslice_write_block(32711568, 64, 1)
t582[23]=t25[23] # fslice_write_block(32711568, 64, 1)
t582[24]=t25[24] # fslice_write_block(32711568, 64, 1)
t582[25]=t25[25] # fslice_write_block(32711568, 64, 1)
t582[26]=t25[26] # fslice_write_block(32711568, 64, 1)
t582[27]=t25[27] # fslice_write_block(32711568, 64, 1)
t582[28]=t25[28] # fslice_write_block(32711568, 64, 1)
t582[29]=t25[29] # fslice_write_block(32711568, 64, 1)
t582[30]=t25[30] # fslice_write_block(32711568, 64, 1)
t582[31]=t25[31] # fslice_write_block(32711568, 64, 1)
t582[32]=t25[32] # fslice_write_block(32711568, 64, 1)
t582[33]=t25[33] # fslice_write_block(32711568, 64, 1)
t582[34]=t25[34] # fslice_write_block(32711568, 64, 1)
t582[35]=t25[35] # fslice_write_block(32711568, 64, 1)
t582[36]=t25[36] # fslice_write_block(32711568, 64, 1)
t582[37]=t25[37] # fslice_write_block(32711568, 64, 1)
t582[38]=t25[38] # fslice_write_block(32711568, 64, 1)
t582[39]=t25[39] # fslice_write_block(32711568, 64, 1)
t582[40]=t25[40] # fslice_write_block(32711568, 64, 1)
t582[41]=t25[41] # fslice_write_block(32711568, 64, 1)
t582[42]=t25[42] # fslice_write_block(32711568, 64, 1)
t582[43]=t25[43] # fslice_write_block(32711568, 64, 1)
t582[44]=t25[44] # fslice_write_block(32711568, 64, 1)
t582[45]=t25[45] # fslice_write_block(32711568, 64, 1)
t582[46]=t25[46] # fslice_write_block(32711568, 64, 1)
t582[47]=t25[47] # fslice_write_block(32711568, 64, 1)
t582[48]=t25[48] # fslice_write_block(32711568, 64, 1)
t582[49]=t25[49] # fslice_write_block(32711568, 64, 1)
t582[50]=t25[50] # fslice_write_block(32711568, 64, 1)
t582[51]=t25[51] # fslice_write_block(32711568, 64, 1)
t582[52]=t25[52] # fslice_write_block(32711568, 64, 1)
t582[53]=t25[53] # fslice_write_block(32711568, 64, 1)
t582[54]=t25[54] # fslice_write_block(32711568, 64, 1)
t582[55]=t25[55] # fslice_write_block(32711568, 64, 1)
t582[56]=t25[56] # fslice_write_block(32711568, 64, 1)
t582[57]=t25[57] # fslice_write_block(32711568, 64, 1)
t582[58]=t25[58] # fslice_write_block(32711568, 64, 1)
t582[59]=t25[59] # fslice_write_block(32711568, 64, 1)
t582[60]=t25[60] # fslice_write_block(32711568, 64, 1)
t582[61]=t25[61] # fslice_write_block(32711568, 64, 1)
t582[62]=t25[62] # fslice_write_block(32711568, 64, 1)
t582[63]=t25[63] # fslice_write_block(32711568, 64, 1)
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
# SSSS Returning back from functionwrite_blocks
# SSSS Returning back from functiontestfs_write_inode_freemap
# SSSS Returning back from functiontestfs_get_inode_freemap
#fslice_value = 0
#fslice_value = 0
ICMP(t576,t1,'ICMP_ULE')
# testfs_get_inode()
# SSSS Calling function testfs_get_inode
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
# inode_hash_find()
# SSSS Calling function inode_hash_find
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 8
# hash_int()
# SSSS Calling function hash_int
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2654404609
t583=A("mul",t576,t483, 583)
#fslice_value = 0
#fslice_value = 32
t584=A("lshr",t583,t486, 584)
# SSSS Returning back from functionhash_int
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
# SSSS Returning back from functioninode_hash_find
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 72
t585=M(72, 0, 585,t2,t4)
#fslice_value = 0
ICMP(t0,t0,'ICMP_EQ')
#fslice_value = 0
#fslice_value = 1
# testfs_read_inode_block()
# SSSS Calling function testfs_read_inode_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
# testfs_inode_to_block_nr()
# SSSS Calling function testfs_inode_to_block_nr
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2
t586=A("udiv",t576,t35, 586)
#fslice_value = 0
#fslice_value = 0
ICMP(t586,t1,'ICMP_ULT')
#fslice_value = 128
ICMP(t586,t490,'ICMP_ULE')
# SSSS Returning back from functiontestfs_inode_to_block_nr
#fslice_value = 0
t587=A("add",t491,t586, 587)#SWITCH 491 0
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 8:read_blocks()--->testfs_read_inode_block()--->testfs_get_inode()--->testfs_create_inode()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t588=A("mul",t587,t7, 588)
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
t589=A("add",t587,t1, 589)
#fslice_value = 64
#gBlockTAINT 590
t590=B(64,64,t7,t589, 590) # GetBlock(64, 64) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_read_inode_block
# testfs_inode_to_block_offset()
# SSSS Calling function testfs_inode_to_block_offset
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2
t591=A("urem",t576,t35, 591)
#fslice_value = 32
t592=A("mul",t591,t485, 592)
#fslice_value = 0
#fslice_value = 0
ICMP(t592,t1,'ICMP_ULT')
#fslice_value = 64
ICMP(t592,t7,'ICMP_ULE')
# SSSS Returning back from functiontestfs_inode_to_block_offset
#fslice_value = 0
t585[4]=t590[32] # fslice_memmove
t585[5]=t590[33] # fslice_memmove
t585[6]=t590[34] # fslice_memmove
t585[7]=t590[35] # fslice_memmove
t585[8]=t590[36] # fslice_memmove
t585[9]=t590[37] # fslice_memmove
t585[10]=t590[38] # fslice_memmove
t585[11]=t590[39] # fslice_memmove
t585[12]=t590[40] # fslice_memmove
t585[13]=t590[41] # fslice_memmove
t585[14]=t590[42] # fslice_memmove
t585[15]=t590[43] # fslice_memmove
t585[16]=t590[44] # fslice_memmove
t585[17]=t590[45] # fslice_memmove
t585[18]=t590[46] # fslice_memmove
t585[19]=t590[47] # fslice_memmove
t585[20]=t590[48] # fslice_memmove
t585[21]=t590[49] # fslice_memmove
t585[22]=t590[50] # fslice_memmove
t585[23]=t590[51] # fslice_memmove
t585[24]=t590[52] # fslice_memmove
t585[25]=t590[53] # fslice_memmove
t585[26]=t590[54] # fslice_memmove
t585[27]=t590[55] # fslice_memmove
t585[28]=t590[56] # fslice_memmove
t585[29]=t590[57] # fslice_memmove
t585[30]=t590[58] # fslice_memmove
t585[31]=t590[59] # fslice_memmove
t585[32]=t590[60] # fslice_memmove
t585[33]=t590[61] # fslice_memmove
t585[34]=t590[62] # fslice_memmove
t585[35]=t590[63] # fslice_memmove
#DSTRUCT:t590,32:Size|32
#testfs_get_inode:&in->in
#testfs_get_inode:block + block_offset
# inode_hash_insert()
# SSSS Calling function inode_hash_insert
#fslice_value = 0
#fslice_value = 0
# INIT_HLIST_NODE()
# SSSS Calling function INIT_HLIST_NODE
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functionINIT_HLIST_NODE
#fslice_value = 8
# hash_int()
# SSSS Calling function hash_int
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2654404609
#fslice_value = 0
#fslice_value = 32
# SSSS Returning back from functionhash_int
# hlist_add_head()
# SSSS Calling function hlist_add_head
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# SSSS Returning back from functionhlist_add_head
# SSSS Returning back from functioninode_hash_insert
# SSSS Returning back from functiontestfs_get_inode
#fslice_value = 0
#fslice_value = 1
t593=A("or",t1,t2, 593)
#fslice_value = 0
# SSSS Returning back from functiontestfs_create_inode
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# testfs_inode_get_nr()
# SSSS Calling function testfs_inode_get_nr
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_nr
#fslice_value = 0
#fslice_value = 2
ICMP(t35,t35,'ICMP_EQ')
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_nr()
# SSSS Calling function testfs_inode_get_nr
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_nr
#fslice_value = 0
# testfs_create_empty_dir()
# SSSS Calling function testfs_create_empty_dir
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t35,t35,'ICMP_EQ')
# testfs_inode_get_nr()
# SSSS Calling function testfs_inode_get_nr
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_nr
# testfs_add_dirent()
# SSSS Calling function testfs_add_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t594=A("add",t0,t2, 594)
#fslice_value = 0
t595=N(2, 595)
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t35,t35,'ICMP_EQ')
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
#fslice_value = 0
# testfs_next_dirent()
# SSSS Calling function testfs_next_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t35,t35,'ICMP_EQ')
# testfs_inode_get_size()
# SSSS Calling function testfs_inode_get_size
#fslice_value = 0
#fslice_value = 0
 #YYY assigned new taint id = 590 taint id checked for = 590
t596=O(t590,596,t590[36],t590[37],t590[38],t590[39]) # Load(32855336, 4)
# SSSS Returning back from functiontestfs_inode_get_size
ICMP(t1,t596,'ICMP_ULT')
# SSSS Returning back from functiontestfs_next_dirent
#fslice_value = 0
ICMP(t0,t0,'ICMP_EQ')
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t1,t1,'ICMP_UGT')
# testfs_inode_get_size()
# SSSS Calling function testfs_inode_get_size
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_size
ICMP(t1,t596,'ICMP_EQ')
# testfs_write_dirent()
# SSSS Calling function testfs_write_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 8
t597=A("add",t15,t594, 597)
#fslice_value = 0
t598=M(10, 0, 598,t597)
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t576,t1,'ICMP_ULT')
t598[8]=t595[0] # fslice_memmove
t598[9]=t595[1] # fslice_memmove
#DSTRUCT:t595,0:Size|2
#testfs_write_dirent:D_NAME(d)
#testfs_write_dirent:name
t599=A("add",t1,t597, 599)
#fslice_value = 64
t600=A("sdiv",t599,t7, 600)
#fslice_value = 64
ICMP(t600,t524,'ICMP_UGE')
# testfs_write_data()
# SSSS Calling function testfs_write_data
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
t601=D(10, 601)
t601[0]=t594[0]
t601[1]=t594[1]
t601[2]=t594[2]
t601[3]=t594[3]
t601[4]=t576[0]
t601[5]=t576[1]
t601[6]=t576[2]
t601[7]=t576[3]
t601[8]=t595[0]
t601[9]=t595[1]
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 64
ICMP(t1,t596,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 64
#fslice_value = 0
# testfs_allocate_block()
# SSSS Calling function testfs_allocate_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t526,t1,'ICMP_ULT')
# testfs_get_block()
# SSSS Calling function testfs_get_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t526,t1,'ICMP_ULT')
#fslice_value = 4
ICMP(t526,t527,'ICMP_ULE')
 #YYY assigned new taint id = 590 taint id checked for = 590
t602=O(t590,602,t590[44],t590[45],t590[46],t590[47]) # Load(32855344, 4)
#fslice_value = 0
#fslice_value = 0
ICMP(t602,t1,'ICMP_UGE')
# SSSS Returning back from functiontestfs_get_block
#fslice_value = 0
#fslice_value = 0
ICMP(t602,t1,'ICMP_UGT')
#fslice_value = 4
ICMP(t526,t527,'ICMP_ULE')
# testfs_alloc_block()
# SSSS Calling function testfs_alloc_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
# testfs_get_block_freemap()
# SSSS Calling function testfs_get_block_freemap
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# bitmap_alloc()
# SSSS Calling function bitmap_alloc
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 8
#fslice_value = 1
#fslice_value = 8
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t30,'ICMP_ULE')
 #YYY assigned new taint id = 38 taint id checked for = 38
t603=O(t38,603,t38[0]) # Load(32714832, 1)
#fslice_value = 255
ICMP(t603,t569,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 8
ICMP(t1,t15,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
t604=A("and",t603,t570, 604)#SWITCH 603 2
#fslice_value = 0
ICMP(t604,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 8
ICMP(t11,t15,'ICMP_ULE')
#fslice_value = 1
#fslice_value = 0
t605=A("and",t603,t572, 605)#SWITCH 603 2
#fslice_value = 0
ICMP(t605,t1,'ICMP_EQ')
t606=A("or",t603,t572, 606)#SWITCH 603 2
#fslice_value = 8
ICMP(t576,t26,'ICMP_ULE')
#fslice_value = 0
# SSSS Returning back from functionbitmap_alloc
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# testfs_write_block_freemap()
# SSSS Calling function testfs_write_block_freemap
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# bitmap_getdata()
# SSSS Calling function bitmap_getdata
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functionbitmap_getdata
#fslice_value = 0
#fslice_value = 512
#fslice_value = 0
#fslice_value = 64
t607=A("add",t34,t577, 607)#SWITCH 34 0
#fslice_value = 1
# write_blocks()
# SSSS Calling function write_blocks
# SSSS CALL STACK 13:write_blocks()--->testfs_write_block_freemap()--->testfs_get_block_freemap()--->testfs_alloc_block()--->testfs_allocate_block()--->testfs_write_data()--->testfs_write_dirent()--->testfs_add_dirent()--->testfs_create_empty_dir()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t608=A("mul",t607,t7, 608)
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
t609=A("add",t607,t1, 609)
#fslice_value = 64
#gBlockTAINT 610
t610=B(64,2,t7,t609, 610) # GetBlock(64, 2) w
t610[0]=t606[0] # fslice_write_block(32714832, 64, 2)
t610[1]=t38[1] # fslice_write_block(32714832, 64, 2)
t610[2]=t38[2] # fslice_write_block(32714832, 64, 2)
t610[3]=t38[3] # fslice_write_block(32714832, 64, 2)
t610[4]=t38[4] # fslice_write_block(32714832, 64, 2)
t610[5]=t38[5] # fslice_write_block(32714832, 64, 2)
t610[6]=t38[6] # fslice_write_block(32714832, 64, 2)
t610[7]=t38[7] # fslice_write_block(32714832, 64, 2)
t610[8]=t38[8] # fslice_write_block(32714832, 64, 2)
t610[9]=t38[9] # fslice_write_block(32714832, 64, 2)
t610[10]=t38[10] # fslice_write_block(32714832, 64, 2)
t610[11]=t38[11] # fslice_write_block(32714832, 64, 2)
t610[12]=t38[12] # fslice_write_block(32714832, 64, 2)
t610[13]=t38[13] # fslice_write_block(32714832, 64, 2)
t610[14]=t38[14] # fslice_write_block(32714832, 64, 2)
t610[15]=t38[15] # fslice_write_block(32714832, 64, 2)
t610[16]=t38[16] # fslice_write_block(32714832, 64, 2)
t610[17]=t38[17] # fslice_write_block(32714832, 64, 2)
t610[18]=t38[18] # fslice_write_block(32714832, 64, 2)
t610[19]=t38[19] # fslice_write_block(32714832, 64, 2)
t610[20]=t38[20] # fslice_write_block(32714832, 64, 2)
t610[21]=t38[21] # fslice_write_block(32714832, 64, 2)
t610[22]=t38[22] # fslice_write_block(32714832, 64, 2)
t610[23]=t38[23] # fslice_write_block(32714832, 64, 2)
t610[24]=t38[24] # fslice_write_block(32714832, 64, 2)
t610[25]=t38[25] # fslice_write_block(32714832, 64, 2)
t610[26]=t38[26] # fslice_write_block(32714832, 64, 2)
t610[27]=t38[27] # fslice_write_block(32714832, 64, 2)
t610[28]=t38[28] # fslice_write_block(32714832, 64, 2)
t610[29]=t38[29] # fslice_write_block(32714832, 64, 2)
t610[30]=t38[30] # fslice_write_block(32714832, 64, 2)
t610[31]=t38[31] # fslice_write_block(32714832, 64, 2)
t610[32]=t38[32] # fslice_write_block(32714832, 64, 2)
t610[33]=t38[33] # fslice_write_block(32714832, 64, 2)
t610[34]=t38[34] # fslice_write_block(32714832, 64, 2)
t610[35]=t38[35] # fslice_write_block(32714832, 64, 2)
t610[36]=t38[36] # fslice_write_block(32714832, 64, 2)
t610[37]=t38[37] # fslice_write_block(32714832, 64, 2)
t610[38]=t38[38] # fslice_write_block(32714832, 64, 2)
t610[39]=t38[39] # fslice_write_block(32714832, 64, 2)
t610[40]=t38[40] # fslice_write_block(32714832, 64, 2)
t610[41]=t38[41] # fslice_write_block(32714832, 64, 2)
t610[42]=t38[42] # fslice_write_block(32714832, 64, 2)
t610[43]=t38[43] # fslice_write_block(32714832, 64, 2)
t610[44]=t38[44] # fslice_write_block(32714832, 64, 2)
t610[45]=t38[45] # fslice_write_block(32714832, 64, 2)
t610[46]=t38[46] # fslice_write_block(32714832, 64, 2)
t610[47]=t38[47] # fslice_write_block(32714832, 64, 2)
t610[48]=t38[48] # fslice_write_block(32714832, 64, 2)
t610[49]=t38[49] # fslice_write_block(32714832, 64, 2)
t610[50]=t38[50] # fslice_write_block(32714832, 64, 2)
t610[51]=t38[51] # fslice_write_block(32714832, 64, 2)
t610[52]=t38[52] # fslice_write_block(32714832, 64, 2)
t610[53]=t38[53] # fslice_write_block(32714832, 64, 2)
t610[54]=t38[54] # fslice_write_block(32714832, 64, 2)
t610[55]=t38[55] # fslice_write_block(32714832, 64, 2)
t610[56]=t38[56] # fslice_write_block(32714832, 64, 2)
t610[57]=t38[57] # fslice_write_block(32714832, 64, 2)
t610[58]=t38[58] # fslice_write_block(32714832, 64, 2)
t610[59]=t38[59] # fslice_write_block(32714832, 64, 2)
t610[60]=t38[60] # fslice_write_block(32714832, 64, 2)
t610[61]=t38[61] # fslice_write_block(32714832, 64, 2)
t610[62]=t38[62] # fslice_write_block(32714832, 64, 2)
t610[63]=t38[63] # fslice_write_block(32714832, 64, 2)
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
# SSSS Returning back from functionwrite_blocks
# SSSS Returning back from functiontestfs_write_block_freemap
# SSSS Returning back from functiontestfs_get_block_freemap
#fslice_value = 0
#fslice_value = 0
ICMP(t576,t1,'ICMP_ULE')
#testfs_alloc_block:block
 #YYY assigned new taint id = 10 taint id checked for = 10
t611=O(t10,611,t10[16],t10[17],t10[18],t10[19]) # Load(32700656, 4)
t612=A("add",t611,t576, 612)#SWITCH 611 0
# SSSS Returning back from functiontestfs_alloc_block
#fslice_value = 0
#fslice_value = 0
ICMP(t612,t1,'ICMP_ULE')
#fslice_value = 1
t613=A("or",t593,t2, 613)
# SSSS Returning back from functiontestfs_allocate_block
#fslice_value = 0
#fslice_value = 0
ICMP(t612,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t612,t1,'ICMP_UGE')
t614=A("sub",t597,t1, 614)
#fslice_value = 64
ICMP(t614,t533,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t1[0]=t601[0] # fslice_memmove
t1[1]=t601[1] # fslice_memmove
t1[2]=t601[2] # fslice_memmove
t1[3]=t601[3] # fslice_memmove
t1[4]=t601[4] # fslice_memmove
t1[5]=t601[5] # fslice_memmove
t1[6]=t601[6] # fslice_memmove
t1[7]=t601[7] # fslice_memmove
t1[8]=t601[8] # fslice_memmove
t1[9]=t601[9] # fslice_memmove
#DSTRUCT:t601,0:Size|10
#testfs_write_data:block + b_offset
#testfs_write_data:buf + buf_offset
#fslice_value = 64
# testfs_calculate_csum()
# SSSS Calling function testfs_calculate_csum
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 4
t615=A("urem",t7,t527, 615)
#fslice_value = 0
ICMP(t615,t1,'ICMP_EQ')
#fslice_value = 4
t616=A("udiv",t7,t527, 616)
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t616,'ICMP_ULE')
 #YYY assigned new taint id = 601 taint id checked for = 601
t617=O(t601,617,t601[0],t601[1],t601[2],t601[3]) # Load(140727937605200, 4)
t618=A("xor",t1,t617, 618)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t616,'ICMP_ULE')
 #YYY assigned new taint id = 601 taint id checked for = 601
t619=O(t601,619,t601[4],t601[5],t601[6],t601[7]) # Load(140727937605204, 4)
t620=A("xor",t618,t619, 620)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t42,t616,'ICMP_ULE')
 #XXX assigned new taint id = 601 taint id checked for = 1
t621=O(t601,621,t601[8],t601[9],t1[10],t1[11]) # Load(140727937605208, 4)
t622=A("xor",t620,t621, 622)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t55,t616,'ICMP_ULE')
 #YYY assigned new taint id = 1 taint id checked for = 1
t623=O(t1,623,t1[12],t1[13],t1[14],t1[15]) # Load(140727937605212, 4)
t624=A("xor",t622,t623, 624)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t59,t616,'ICMP_ULE')
 #YYY assigned new taint id = 1 taint id checked for = 1
t625=O(t1,625,t1[16],t1[17],t1[18],t1[19]) # Load(140727937605216, 4)
t626=A("xor",t624,t625, 626)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t63,t616,'ICMP_ULE')
 #YYY assigned new taint id = 1 taint id checked for = 1
t627=O(t1,627,t1[20],t1[21],t1[22],t1[23]) # Load(140727937605220, 4)
t628=A("xor",t626,t627, 628)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t67,t616,'ICMP_ULE')
 #YYY assigned new taint id = 1 taint id checked for = 1
t629=O(t1,629,t1[24],t1[25],t1[26],t1[27]) # Load(140727937605224, 4)
t630=A("xor",t628,t629, 630)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t71,t616,'ICMP_ULE')
 #YYY assigned new taint id = 1 taint id checked for = 1
t631=O(t1,631,t1[28],t1[29],t1[30],t1[31]) # Load(140727937605228, 4)
t632=A("xor",t630,t631, 632)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t75,t616,'ICMP_ULE')
 #YYY assigned new taint id = 1 taint id checked for = 1
t633=O(t1,633,t1[32],t1[33],t1[34],t1[35]) # Load(140727937605232, 4)
t634=A("xor",t632,t633, 634)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t79,t616,'ICMP_ULE')
 #YYY assigned new taint id = 1 taint id checked for = 1
t635=O(t1,635,t1[36],t1[37],t1[38],t1[39]) # Load(140727937605236, 4)
t636=A("xor",t634,t635, 636)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t83,t616,'ICMP_ULE')
 #YYY assigned new taint id = 1 taint id checked for = 1
t637=O(t1,637,t1[40],t1[41],t1[42],t1[43]) # Load(140727937605240, 4)
t638=A("xor",t636,t637, 638)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t87,t616,'ICMP_ULE')
 #YYY assigned new taint id = 1 taint id checked for = 1
t639=O(t1,639,t1[44],t1[45],t1[46],t1[47]) # Load(140727937605244, 4)
t640=A("xor",t638,t639, 640)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t91,t616,'ICMP_ULE')
 #YYY assigned new taint id = 1 taint id checked for = 1
t641=O(t1,641,t1[48],t1[49],t1[50],t1[51]) # Load(140727937605248, 4)
t642=A("xor",t640,t641, 642)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t95,t616,'ICMP_ULE')
 #YYY assigned new taint id = 1 taint id checked for = 1
t643=O(t1,643,t1[52],t1[53],t1[54],t1[55]) # Load(140727937605252, 4)
t644=A("xor",t642,t643, 644)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t99,t616,'ICMP_ULE')
 #YYY assigned new taint id = 1 taint id checked for = 1
t645=O(t1,645,t1[56],t1[57],t1[58],t1[59]) # Load(140727937605256, 4)
t646=A("xor",t644,t645, 646)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t103,t616,'ICMP_ULE')
t647=A("xor",t646,t1, 647)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t107,t616,'ICMP_ULE')
# SSSS Returning back from functiontestfs_calculate_csum
#fslice_value = 0
#fslice_value = 1
# write_blocks()
# SSSS Calling function write_blocks
# SSSS CALL STACK 9:write_blocks()--->testfs_write_data()--->testfs_write_dirent()--->testfs_add_dirent()--->testfs_create_empty_dir()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t648=A("mul",t612,t7, 648)
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
t649=A("add",t612,t1, 649)
#fslice_value = 64
#gBlockTAINT 650
t650=B(64,193,t7,t649, 650) # GetBlock(64, 193) w
t650[0]=t601[0] # fslice_write_block(140727937605200, 64, 193)
t650[1]=t601[1] # fslice_write_block(140727937605200, 64, 193)
t650[2]=t601[2] # fslice_write_block(140727937605200, 64, 193)
t650[3]=t601[3] # fslice_write_block(140727937605200, 64, 193)
t650[4]=t601[4] # fslice_write_block(140727937605200, 64, 193)
t650[5]=t601[5] # fslice_write_block(140727937605200, 64, 193)
t650[6]=t601[6] # fslice_write_block(140727937605200, 64, 193)
t650[7]=t601[7] # fslice_write_block(140727937605200, 64, 193)
t650[8]=t601[8] # fslice_write_block(140727937605200, 64, 193)
t650[9]=t601[9] # fslice_write_block(140727937605200, 64, 193)
t650[10]=t1[10] # fslice_write_block(140727937605200, 64, 193)
t650[11]=t1[11] # fslice_write_block(140727937605200, 64, 193)
t650[12]=t1[12] # fslice_write_block(140727937605200, 64, 193)
t650[13]=t1[13] # fslice_write_block(140727937605200, 64, 193)
t650[14]=t1[14] # fslice_write_block(140727937605200, 64, 193)
t650[15]=t1[15] # fslice_write_block(140727937605200, 64, 193)
t650[16]=t1[16] # fslice_write_block(140727937605200, 64, 193)
t650[17]=t1[17] # fslice_write_block(140727937605200, 64, 193)
t650[18]=t1[18] # fslice_write_block(140727937605200, 64, 193)
t650[19]=t1[19] # fslice_write_block(140727937605200, 64, 193)
t650[20]=t1[20] # fslice_write_block(140727937605200, 64, 193)
t650[21]=t1[21] # fslice_write_block(140727937605200, 64, 193)
t650[22]=t1[22] # fslice_write_block(140727937605200, 64, 193)
t650[23]=t1[23] # fslice_write_block(140727937605200, 64, 193)
t650[24]=t1[24] # fslice_write_block(140727937605200, 64, 193)
t650[25]=t1[25] # fslice_write_block(140727937605200, 64, 193)
t650[26]=t1[26] # fslice_write_block(140727937605200, 64, 193)
t650[27]=t1[27] # fslice_write_block(140727937605200, 64, 193)
t650[28]=t1[28] # fslice_write_block(140727937605200, 64, 193)
t650[29]=t1[29] # fslice_write_block(140727937605200, 64, 193)
t650[30]=t1[30] # fslice_write_block(140727937605200, 64, 193)
t650[31]=t1[31] # fslice_write_block(140727937605200, 64, 193)
t650[32]=t1[32] # fslice_write_block(140727937605200, 64, 193)
t650[33]=t1[33] # fslice_write_block(140727937605200, 64, 193)
t650[34]=t1[34] # fslice_write_block(140727937605200, 64, 193)
t650[35]=t1[35] # fslice_write_block(140727937605200, 64, 193)
t650[36]=t1[36] # fslice_write_block(140727937605200, 64, 193)
t650[37]=t1[37] # fslice_write_block(140727937605200, 64, 193)
t650[38]=t1[38] # fslice_write_block(140727937605200, 64, 193)
t650[39]=t1[39] # fslice_write_block(140727937605200, 64, 193)
t650[40]=t1[40] # fslice_write_block(140727937605200, 64, 193)
t650[41]=t1[41] # fslice_write_block(140727937605200, 64, 193)
t650[42]=t1[42] # fslice_write_block(140727937605200, 64, 193)
t650[43]=t1[43] # fslice_write_block(140727937605200, 64, 193)
t650[44]=t1[44] # fslice_write_block(140727937605200, 64, 193)
t650[45]=t1[45] # fslice_write_block(140727937605200, 64, 193)
t650[46]=t1[46] # fslice_write_block(140727937605200, 64, 193)
t650[47]=t1[47] # fslice_write_block(140727937605200, 64, 193)
t650[48]=t1[48] # fslice_write_block(140727937605200, 64, 193)
t650[49]=t1[49] # fslice_write_block(140727937605200, 64, 193)
t650[50]=t1[50] # fslice_write_block(140727937605200, 64, 193)
t650[51]=t1[51] # fslice_write_block(140727937605200, 64, 193)
t650[52]=t1[52] # fslice_write_block(140727937605200, 64, 193)
t650[53]=t1[53] # fslice_write_block(140727937605200, 64, 193)
t650[54]=t1[54] # fslice_write_block(140727937605200, 64, 193)
t650[55]=t1[55] # fslice_write_block(140727937605200, 64, 193)
t650[56]=t1[56] # fslice_write_block(140727937605200, 64, 193)
t650[57]=t1[57] # fslice_write_block(140727937605200, 64, 193)
t650[58]=t1[58] # fslice_write_block(140727937605200, 64, 193)
t650[59]=t1[59] # fslice_write_block(140727937605200, 64, 193)
t650[60]=t1[60] # fslice_write_block(140727937605200, 64, 193)
t650[61]=t1[61] # fslice_write_block(140727937605200, 64, 193)
t650[62]=t1[62] # fslice_write_block(140727937605200, 64, 193)
t650[63]=t1[63] # fslice_write_block(140727937605200, 64, 193)
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
# SSSS Returning back from functionwrite_blocks
# testfs_put_csum()
# SSSS Calling function testfs_put_csum
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
t651=A("sub",t612,t611, 651)
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t651,t1,'ICMP_ULT')
#fslice_value = 960
t652=V(960, 652) # Taint<652, 0, 0>
ICMP(t651,t652,'ICMP_ULE')
# testfs_write_csum()
# SSSS Calling function testfs_write_csum
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 4
t653=A("mul",t651,t527, 653)
#fslice_value = 64
t654=A("udiv",t653,t7, 654)
#fslice_value = 64
t655=A("mul",t654,t7, 655)
t656=A("add",t45,t654, 656)#SWITCH 45 0
#fslice_value = 1
# write_blocks()
# SSSS Calling function write_blocks
# SSSS CALL STACK 11:write_blocks()--->testfs_write_csum()--->testfs_put_csum()--->testfs_write_data()--->testfs_write_dirent()--->testfs_add_dirent()--->testfs_create_empty_dir()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t657=A("mul",t656,t7, 657)
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
t658=A("add",t656,t1, 658)
#fslice_value = 64
#gBlockTAINT 659
t659=B(64,4,t7,t658, 659) # GetBlock(64, 4) w
t659[0]=t49[0] # fslice_write_block(32723328, 64, 4)
t659[1]=t49[1] # fslice_write_block(32723328, 64, 4)
t659[2]=t49[2] # fslice_write_block(32723328, 64, 4)
t659[3]=t49[3] # fslice_write_block(32723328, 64, 4)
t659[4]=t647[0] # fslice_write_block(32723328, 64, 4)
t659[5]=t647[1] # fslice_write_block(32723328, 64, 4)
t659[6]=t647[2] # fslice_write_block(32723328, 64, 4)
t659[7]=t647[3] # fslice_write_block(32723328, 64, 4)
t659[8]=t49[8] # fslice_write_block(32723328, 64, 4)
t659[9]=t49[9] # fslice_write_block(32723328, 64, 4)
t659[10]=t49[10] # fslice_write_block(32723328, 64, 4)
t659[11]=t49[11] # fslice_write_block(32723328, 64, 4)
t659[12]=t49[12] # fslice_write_block(32723328, 64, 4)
t659[13]=t49[13] # fslice_write_block(32723328, 64, 4)
t659[14]=t49[14] # fslice_write_block(32723328, 64, 4)
t659[15]=t49[15] # fslice_write_block(32723328, 64, 4)
t659[16]=t49[16] # fslice_write_block(32723328, 64, 4)
t659[17]=t49[17] # fslice_write_block(32723328, 64, 4)
t659[18]=t49[18] # fslice_write_block(32723328, 64, 4)
t659[19]=t49[19] # fslice_write_block(32723328, 64, 4)
t659[20]=t49[20] # fslice_write_block(32723328, 64, 4)
t659[21]=t49[21] # fslice_write_block(32723328, 64, 4)
t659[22]=t49[22] # fslice_write_block(32723328, 64, 4)
t659[23]=t49[23] # fslice_write_block(32723328, 64, 4)
t659[24]=t49[24] # fslice_write_block(32723328, 64, 4)
t659[25]=t49[25] # fslice_write_block(32723328, 64, 4)
t659[26]=t49[26] # fslice_write_block(32723328, 64, 4)
t659[27]=t49[27] # fslice_write_block(32723328, 64, 4)
t659[28]=t49[28] # fslice_write_block(32723328, 64, 4)
t659[29]=t49[29] # fslice_write_block(32723328, 64, 4)
t659[30]=t49[30] # fslice_write_block(32723328, 64, 4)
t659[31]=t49[31] # fslice_write_block(32723328, 64, 4)
t659[32]=t49[32] # fslice_write_block(32723328, 64, 4)
t659[33]=t49[33] # fslice_write_block(32723328, 64, 4)
t659[34]=t49[34] # fslice_write_block(32723328, 64, 4)
t659[35]=t49[35] # fslice_write_block(32723328, 64, 4)
t659[36]=t49[36] # fslice_write_block(32723328, 64, 4)
t659[37]=t49[37] # fslice_write_block(32723328, 64, 4)
t659[38]=t49[38] # fslice_write_block(32723328, 64, 4)
t659[39]=t49[39] # fslice_write_block(32723328, 64, 4)
t659[40]=t49[40] # fslice_write_block(32723328, 64, 4)
t659[41]=t49[41] # fslice_write_block(32723328, 64, 4)
t659[42]=t49[42] # fslice_write_block(32723328, 64, 4)
t659[43]=t49[43] # fslice_write_block(32723328, 64, 4)
t659[44]=t49[44] # fslice_write_block(32723328, 64, 4)
t659[45]=t49[45] # fslice_write_block(32723328, 64, 4)
t659[46]=t49[46] # fslice_write_block(32723328, 64, 4)
t659[47]=t49[47] # fslice_write_block(32723328, 64, 4)
t659[48]=t49[48] # fslice_write_block(32723328, 64, 4)
t659[49]=t49[49] # fslice_write_block(32723328, 64, 4)
t659[50]=t49[50] # fslice_write_block(32723328, 64, 4)
t659[51]=t49[51] # fslice_write_block(32723328, 64, 4)
t659[52]=t49[52] # fslice_write_block(32723328, 64, 4)
t659[53]=t49[53] # fslice_write_block(32723328, 64, 4)
t659[54]=t49[54] # fslice_write_block(32723328, 64, 4)
t659[55]=t49[55] # fslice_write_block(32723328, 64, 4)
t659[56]=t49[56] # fslice_write_block(32723328, 64, 4)
t659[57]=t49[57] # fslice_write_block(32723328, 64, 4)
t659[58]=t49[58] # fslice_write_block(32723328, 64, 4)
t659[59]=t49[59] # fslice_write_block(32723328, 64, 4)
t659[60]=t49[60] # fslice_write_block(32723328, 64, 4)
t659[61]=t49[61] # fslice_write_block(32723328, 64, 4)
t659[62]=t49[62] # fslice_write_block(32723328, 64, 4)
t659[63]=t49[63] # fslice_write_block(32723328, 64, 4)
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
# SSSS Returning back from functionwrite_blocks
# SSSS Returning back from functiontestfs_write_csum
# SSSS Returning back from functiontestfs_put_csum
t660=A("add",t1,t614, 660)
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 1
ICMP(t596,t599,'ICMP_ULT')
#fslice_value = 1
t661=A("or",t613,t2, 661)
#fslice_value = 0
# SSSS Returning back from functiontestfs_write_data
#fslice_value = 0
# SSSS Returning back from functiontestfs_write_dirent
# SSSS Returning back from functiontestfs_add_dirent
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# testfs_add_dirent()
# SSSS Calling function testfs_add_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
t662=N(3, 662)
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t35,t35,'ICMP_EQ')
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
#fslice_value = 0
# testfs_next_dirent()
# SSSS Calling function testfs_next_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t35,t35,'ICMP_EQ')
# testfs_inode_get_size()
# SSSS Calling function testfs_inode_get_size
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_size
ICMP(t1,t599,'ICMP_ULT')
#fslice_value = 8
#fslice_value = 64
#fslice_value = 64
ICMP(t523,t524,'ICMP_UGE')
#fslice_value = 8
# testfs_read_data()
# SSSS Calling function testfs_read_data
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 64
ICMP(t522,t599,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 64
#fslice_value = 0
# testfs_get_block()
# SSSS Calling function testfs_get_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t526,t1,'ICMP_ULT')
#fslice_value = 4
ICMP(t526,t527,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t612,t1,'ICMP_UGE')
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 10:read_blocks()--->testfs_get_block()--->testfs_read_data()--->testfs_next_dirent()--->testfs_add_dirent()--->testfs_create_empty_dir()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 663
t663=B(64,193,t7,t649, 663) # GetBlock(64, 193) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_get_block
#fslice_value = 0
#fslice_value = 0
ICMP(t612,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t612,t1,'ICMP_UGE')
#fslice_value = 64
ICMP(t532,t533,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
#DSTRUCT:t663,0:Size|8
#testfs_read_data:buf + buf_offset
#testfs_read_data:block + b_offset
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
# SSSS Returning back from functiontestfs_read_data
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
 #YYY assigned new taint id = 663 taint id checked for = 663
t664=O(t663,664,t663[0],t663[1],t663[2],t663[3]) # Load(140727937607680, 4)
#fslice_value = 0
ICMP(t664,t1,'ICMP_EQ')
#fslice_value = 8
t665=A("add",t15,t664, 665)
t666=M(10, 0, 666,t665)
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
t666[0]=t663[0] # fslice_memmove
t666[1]=t663[1] # fslice_memmove
t666[2]=t663[2] # fslice_memmove
t666[3]=t663[3] # fslice_memmove
t666[4]=t663[4] # fslice_memmove
t666[5]=t663[5] # fslice_memmove
t666[6]=t663[6] # fslice_memmove
t666[7]=t663[7] # fslice_memmove
#DSTRUCT:t663,0:Size|8
#fslice_value = 8
# testfs_read_data()
# SSSS Calling function testfs_read_data
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 64
t667=A("add",t522,t664, 667)
ICMP(t667,t599,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 64
#fslice_value = 0
# testfs_get_block()
# SSSS Calling function testfs_get_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t542,t1,'ICMP_ULT')
#fslice_value = 4
ICMP(t542,t527,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t612,t1,'ICMP_UGE')
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 10:read_blocks()--->testfs_get_block()--->testfs_read_data()--->testfs_next_dirent()--->testfs_add_dirent()--->testfs_create_empty_dir()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 668
t668=B(64,193,t7,t649, 668) # GetBlock(64, 193) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_get_block
#fslice_value = 0
#fslice_value = 0
ICMP(t612,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t612,t1,'ICMP_UGE')
t669=A("sub",t664,t1, 669)#SWITCH 664 193
#fslice_value = 64
ICMP(t669,t545,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t666[8]=t668[8] # fslice_memmove
t666[9]=t668[9] # fslice_memmove
#DSTRUCT:t668,8:Size|2
#testfs_read_data:buf + buf_offset
#testfs_read_data:block + b_offset
t670=A("add",t1,t669, 670)
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
# SSSS Returning back from functiontestfs_read_data
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# SSSS Returning back from functiontestfs_next_dirent
#fslice_value = 0
ICMP(t0,t0,'ICMP_EQ')
t671=O(t663,671,t663[4],t663[5],t663[6],t663[7]) # Load(32889556, 4)
#fslice_value = 0
ICMP(t671,t1,'ICMP_ULT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 0
ICMP(t671,t1,'ICMP_ULT')
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
#fslice_value = 0
# testfs_next_dirent()
# SSSS Calling function testfs_next_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t35,t35,'ICMP_EQ')
# testfs_inode_get_size()
# SSSS Calling function testfs_inode_get_size
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_size
ICMP(t667,t599,'ICMP_ULT')
# SSSS Returning back from functiontestfs_next_dirent
#fslice_value = 0
ICMP(t0,t0,'ICMP_EQ')
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t1,t1,'ICMP_UGT')
# testfs_inode_get_size()
# SSSS Calling function testfs_inode_get_size
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_size
ICMP(t667,t599,'ICMP_EQ')
# testfs_write_dirent()
# SSSS Calling function testfs_write_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 8
#fslice_value = 0
t672=M(11, 0, 672,t597)
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULT')
t672[8]=t662[0] # fslice_memmove
t672[9]=t662[1] # fslice_memmove
t672[10]=t662[2] # fslice_memmove
#DSTRUCT:t662,0:Size|3
#testfs_write_dirent:D_NAME(d)
#testfs_write_dirent:name
t673=A("add",t667,t597, 673)
#fslice_value = 64
t674=A("sdiv",t673,t7, 674)
#fslice_value = 64
t675=A("sdiv",t667,t7, 675)
ICMP(t674,t675,'ICMP_UGE')
# testfs_write_data()
# SSSS Calling function testfs_write_data
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
t676=D(11, 676)
t676[0]=t594[0]
t676[1]=t594[1]
t676[2]=t594[2]
t676[3]=t594[3]
t676[4]=t1[0]
t676[5]=t1[1]
t676[6]=t1[2]
t676[7]=t1[3]
t676[8]=t662[0]
t676[9]=t662[1]
t676[10]=t662[2]
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 64
t677=A("srem",t667,t7, 677)
ICMP(t667,t599,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
t678=A("add",t667,t1, 678)
#fslice_value = 64
t679=A("sdiv",t678,t7, 679)
#fslice_value = 0
# testfs_allocate_block()
# SSSS Calling function testfs_allocate_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t679,t1,'ICMP_ULT')
# testfs_get_block()
# SSSS Calling function testfs_get_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t679,t1,'ICMP_ULT')
#fslice_value = 4
ICMP(t679,t527,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t612,t1,'ICMP_UGE')
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 11:read_blocks()--->testfs_get_block()--->testfs_allocate_block()--->testfs_write_data()--->testfs_write_dirent()--->testfs_add_dirent()--->testfs_create_empty_dir()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 680
t680=B(64,193,t7,t649, 680) # GetBlock(64, 193) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_get_block
#fslice_value = 0
#fslice_value = 0
ICMP(t612,t1,'ICMP_UGT')
# SSSS Returning back from functiontestfs_allocate_block
#fslice_value = 0
#fslice_value = 0
ICMP(t612,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t612,t1,'ICMP_UGE')
#fslice_value = 64
t681=A("sub",t7,t677, 681)
ICMP(t614,t681,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t680[10]=t676[0] # fslice_memmove
t680[11]=t676[1] # fslice_memmove
t680[12]=t676[2] # fslice_memmove
t680[13]=t676[3] # fslice_memmove
t680[14]=t676[4] # fslice_memmove
t680[15]=t676[5] # fslice_memmove
t680[16]=t676[6] # fslice_memmove
t680[17]=t676[7] # fslice_memmove
t680[18]=t676[8] # fslice_memmove
t680[19]=t676[9] # fslice_memmove
t680[20]=t676[10] # fslice_memmove
#DSTRUCT:t676,0:Size|11
#testfs_write_data:block + b_offset
#testfs_write_data:buf + buf_offset
#fslice_value = 64
# testfs_calculate_csum()
# SSSS Calling function testfs_calculate_csum
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 4
#fslice_value = 0
ICMP(t615,t1,'ICMP_EQ')
#fslice_value = 4
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t616,'ICMP_ULE')
 #YYY assigned new taint id = 680 taint id checked for = 680
t682=O(t680,682,t680[0],t680[1],t680[2],t680[3]) # Load(140727937605200, 4)
t683=A("xor",t1,t682, 683)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t616,'ICMP_ULE')
 #YYY assigned new taint id = 680 taint id checked for = 680
t684=O(t680,684,t680[4],t680[5],t680[6],t680[7]) # Load(140727937605204, 4)
t685=A("xor",t683,t684, 685)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t42,t616,'ICMP_ULE')
 #XXX assigned new taint id = 680 taint id checked for = 676
t686=O(t680,686,t680[8],t680[9],t676[0],t676[1]) # Load(140727937605208, 4)
t687=A("xor",t685,t686, 687)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t55,t616,'ICMP_ULE')
 #YYY assigned new taint id = 676 taint id checked for = 676
t688=O(t676,688,t676[2],t676[3],t676[4],t676[5]) # Load(140727937605212, 4)
t689=A("xor",t687,t688, 689)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t59,t616,'ICMP_ULE')
 #YYY assigned new taint id = 676 taint id checked for = 676
t690=O(t676,690,t676[6],t676[7],t676[8],t676[9]) # Load(140727937605216, 4)
t691=A("xor",t689,t690, 691)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t63,t616,'ICMP_ULE')
 #XXX assigned new taint id = 676 taint id checked for = 680
t692=O(t676,692,t676[10],t680[21],t680[22],t680[23]) # Load(140727937605220, 4)
t693=A("xor",t691,t692, 693)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t67,t616,'ICMP_ULE')
 #YYY assigned new taint id = 680 taint id checked for = 680
t694=O(t680,694,t680[24],t680[25],t680[26],t680[27]) # Load(140727937605224, 4)
t695=A("xor",t693,t694, 695)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t71,t616,'ICMP_ULE')
 #YYY assigned new taint id = 680 taint id checked for = 680
t696=O(t680,696,t680[28],t680[29],t680[30],t680[31]) # Load(140727937605228, 4)
t697=A("xor",t695,t696, 697)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t75,t616,'ICMP_ULE')
 #YYY assigned new taint id = 680 taint id checked for = 680
t698=O(t680,698,t680[32],t680[33],t680[34],t680[35]) # Load(140727937605232, 4)
t699=A("xor",t697,t698, 699)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t79,t616,'ICMP_ULE')
 #YYY assigned new taint id = 680 taint id checked for = 680
t700=O(t680,700,t680[36],t680[37],t680[38],t680[39]) # Load(140727937605236, 4)
t701=A("xor",t699,t700, 701)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t83,t616,'ICMP_ULE')
 #YYY assigned new taint id = 680 taint id checked for = 680
t702=O(t680,702,t680[40],t680[41],t680[42],t680[43]) # Load(140727937605240, 4)
t703=A("xor",t701,t702, 703)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t87,t616,'ICMP_ULE')
 #YYY assigned new taint id = 680 taint id checked for = 680
t704=O(t680,704,t680[44],t680[45],t680[46],t680[47]) # Load(140727937605244, 4)
t705=A("xor",t703,t704, 705)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t91,t616,'ICMP_ULE')
 #YYY assigned new taint id = 680 taint id checked for = 680
t706=O(t680,706,t680[48],t680[49],t680[50],t680[51]) # Load(140727937605248, 4)
t707=A("xor",t705,t706, 707)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t95,t616,'ICMP_ULE')
 #YYY assigned new taint id = 680 taint id checked for = 680
t708=O(t680,708,t680[52],t680[53],t680[54],t680[55]) # Load(140727937605252, 4)
t709=A("xor",t707,t708, 709)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t99,t616,'ICMP_ULE')
 #YYY assigned new taint id = 680 taint id checked for = 680
t710=O(t680,710,t680[56],t680[57],t680[58],t680[59]) # Load(140727937605256, 4)
t711=A("xor",t709,t710, 711)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t103,t616,'ICMP_ULE')
t712=O(t680,712,t680[60],t680[61],t680[62],t680[63]) # Load(140727937605260, 4)
t713=A("xor",t711,t712, 713)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t107,t616,'ICMP_ULE')
# SSSS Returning back from functiontestfs_calculate_csum
#fslice_value = 0
#fslice_value = 1
# write_blocks()
# SSSS Calling function write_blocks
# SSSS CALL STACK 9:write_blocks()--->testfs_write_data()--->testfs_write_dirent()--->testfs_add_dirent()--->testfs_create_empty_dir()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 714
t714=B(64,193,t7,t649, 714) # GetBlock(64, 193) w
t714[0]=t680[0] # fslice_write_block(140727937605200, 64, 193)
t714[1]=t680[1] # fslice_write_block(140727937605200, 64, 193)
t714[2]=t680[2] # fslice_write_block(140727937605200, 64, 193)
t714[3]=t680[3] # fslice_write_block(140727937605200, 64, 193)
t714[4]=t680[4] # fslice_write_block(140727937605200, 64, 193)
t714[5]=t680[5] # fslice_write_block(140727937605200, 64, 193)
t714[6]=t680[6] # fslice_write_block(140727937605200, 64, 193)
t714[7]=t680[7] # fslice_write_block(140727937605200, 64, 193)
t714[8]=t680[8] # fslice_write_block(140727937605200, 64, 193)
t714[9]=t680[9] # fslice_write_block(140727937605200, 64, 193)
t714[10]=t676[0] # fslice_write_block(140727937605200, 64, 193)
t714[11]=t676[1] # fslice_write_block(140727937605200, 64, 193)
t714[12]=t676[2] # fslice_write_block(140727937605200, 64, 193)
t714[13]=t676[3] # fslice_write_block(140727937605200, 64, 193)
t714[14]=t676[4] # fslice_write_block(140727937605200, 64, 193)
t714[15]=t676[5] # fslice_write_block(140727937605200, 64, 193)
t714[16]=t676[6] # fslice_write_block(140727937605200, 64, 193)
t714[17]=t676[7] # fslice_write_block(140727937605200, 64, 193)
t714[18]=t676[8] # fslice_write_block(140727937605200, 64, 193)
t714[19]=t676[9] # fslice_write_block(140727937605200, 64, 193)
t714[20]=t676[10] # fslice_write_block(140727937605200, 64, 193)
t714[21]=t680[21] # fslice_write_block(140727937605200, 64, 193)
t714[22]=t680[22] # fslice_write_block(140727937605200, 64, 193)
t714[23]=t680[23] # fslice_write_block(140727937605200, 64, 193)
t714[24]=t680[24] # fslice_write_block(140727937605200, 64, 193)
t714[25]=t680[25] # fslice_write_block(140727937605200, 64, 193)
t714[26]=t680[26] # fslice_write_block(140727937605200, 64, 193)
t714[27]=t680[27] # fslice_write_block(140727937605200, 64, 193)
t714[28]=t680[28] # fslice_write_block(140727937605200, 64, 193)
t714[29]=t680[29] # fslice_write_block(140727937605200, 64, 193)
t714[30]=t680[30] # fslice_write_block(140727937605200, 64, 193)
t714[31]=t680[31] # fslice_write_block(140727937605200, 64, 193)
t714[32]=t680[32] # fslice_write_block(140727937605200, 64, 193)
t714[33]=t680[33] # fslice_write_block(140727937605200, 64, 193)
t714[34]=t680[34] # fslice_write_block(140727937605200, 64, 193)
t714[35]=t680[35] # fslice_write_block(140727937605200, 64, 193)
t714[36]=t680[36] # fslice_write_block(140727937605200, 64, 193)
t714[37]=t680[37] # fslice_write_block(140727937605200, 64, 193)
t714[38]=t680[38] # fslice_write_block(140727937605200, 64, 193)
t714[39]=t680[39] # fslice_write_block(140727937605200, 64, 193)
t714[40]=t680[40] # fslice_write_block(140727937605200, 64, 193)
t714[41]=t680[41] # fslice_write_block(140727937605200, 64, 193)
t714[42]=t680[42] # fslice_write_block(140727937605200, 64, 193)
t714[43]=t680[43] # fslice_write_block(140727937605200, 64, 193)
t714[44]=t680[44] # fslice_write_block(140727937605200, 64, 193)
t714[45]=t680[45] # fslice_write_block(140727937605200, 64, 193)
t714[46]=t680[46] # fslice_write_block(140727937605200, 64, 193)
t714[47]=t680[47] # fslice_write_block(140727937605200, 64, 193)
t714[48]=t680[48] # fslice_write_block(140727937605200, 64, 193)
t714[49]=t680[49] # fslice_write_block(140727937605200, 64, 193)
t714[50]=t680[50] # fslice_write_block(140727937605200, 64, 193)
t714[51]=t680[51] # fslice_write_block(140727937605200, 64, 193)
t714[52]=t680[52] # fslice_write_block(140727937605200, 64, 193)
t714[53]=t680[53] # fslice_write_block(140727937605200, 64, 193)
t714[54]=t680[54] # fslice_write_block(140727937605200, 64, 193)
t714[55]=t680[55] # fslice_write_block(140727937605200, 64, 193)
t714[56]=t680[56] # fslice_write_block(140727937605200, 64, 193)
t714[57]=t680[57] # fslice_write_block(140727937605200, 64, 193)
t714[58]=t680[58] # fslice_write_block(140727937605200, 64, 193)
t714[59]=t680[59] # fslice_write_block(140727937605200, 64, 193)
t714[60]=t680[60] # fslice_write_block(140727937605200, 64, 193)
t714[61]=t680[61] # fslice_write_block(140727937605200, 64, 193)
t714[62]=t680[62] # fslice_write_block(140727937605200, 64, 193)
t714[63]=t680[63] # fslice_write_block(140727937605200, 64, 193)
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
# SSSS Returning back from functionwrite_blocks
# testfs_put_csum()
# SSSS Calling function testfs_put_csum
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t651,t1,'ICMP_ULT')
#fslice_value = 960
ICMP(t651,t652,'ICMP_ULE')
# testfs_write_csum()
# SSSS Calling function testfs_write_csum
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 4
#fslice_value = 64
#fslice_value = 64
#fslice_value = 1
# write_blocks()
# SSSS Calling function write_blocks
# SSSS CALL STACK 11:write_blocks()--->testfs_write_csum()--->testfs_put_csum()--->testfs_write_data()--->testfs_write_dirent()--->testfs_add_dirent()--->testfs_create_empty_dir()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 715
t715=B(64,4,t7,t658, 715) # GetBlock(64, 4) w
t715[0]=t49[0] # fslice_write_block(32723328, 64, 4)
t715[1]=t49[1] # fslice_write_block(32723328, 64, 4)
t715[2]=t49[2] # fslice_write_block(32723328, 64, 4)
t715[3]=t49[3] # fslice_write_block(32723328, 64, 4)
t715[4]=t713[0] # fslice_write_block(32723328, 64, 4)
t715[5]=t713[1] # fslice_write_block(32723328, 64, 4)
t715[6]=t713[2] # fslice_write_block(32723328, 64, 4)
t715[7]=t713[3] # fslice_write_block(32723328, 64, 4)
t715[8]=t49[8] # fslice_write_block(32723328, 64, 4)
t715[9]=t49[9] # fslice_write_block(32723328, 64, 4)
t715[10]=t49[10] # fslice_write_block(32723328, 64, 4)
t715[11]=t49[11] # fslice_write_block(32723328, 64, 4)
t715[12]=t49[12] # fslice_write_block(32723328, 64, 4)
t715[13]=t49[13] # fslice_write_block(32723328, 64, 4)
t715[14]=t49[14] # fslice_write_block(32723328, 64, 4)
t715[15]=t49[15] # fslice_write_block(32723328, 64, 4)
t715[16]=t49[16] # fslice_write_block(32723328, 64, 4)
t715[17]=t49[17] # fslice_write_block(32723328, 64, 4)
t715[18]=t49[18] # fslice_write_block(32723328, 64, 4)
t715[19]=t49[19] # fslice_write_block(32723328, 64, 4)
t715[20]=t49[20] # fslice_write_block(32723328, 64, 4)
t715[21]=t49[21] # fslice_write_block(32723328, 64, 4)
t715[22]=t49[22] # fslice_write_block(32723328, 64, 4)
t715[23]=t49[23] # fslice_write_block(32723328, 64, 4)
t715[24]=t49[24] # fslice_write_block(32723328, 64, 4)
t715[25]=t49[25] # fslice_write_block(32723328, 64, 4)
t715[26]=t49[26] # fslice_write_block(32723328, 64, 4)
t715[27]=t49[27] # fslice_write_block(32723328, 64, 4)
t715[28]=t49[28] # fslice_write_block(32723328, 64, 4)
t715[29]=t49[29] # fslice_write_block(32723328, 64, 4)
t715[30]=t49[30] # fslice_write_block(32723328, 64, 4)
t715[31]=t49[31] # fslice_write_block(32723328, 64, 4)
t715[32]=t49[32] # fslice_write_block(32723328, 64, 4)
t715[33]=t49[33] # fslice_write_block(32723328, 64, 4)
t715[34]=t49[34] # fslice_write_block(32723328, 64, 4)
t715[35]=t49[35] # fslice_write_block(32723328, 64, 4)
t715[36]=t49[36] # fslice_write_block(32723328, 64, 4)
t715[37]=t49[37] # fslice_write_block(32723328, 64, 4)
t715[38]=t49[38] # fslice_write_block(32723328, 64, 4)
t715[39]=t49[39] # fslice_write_block(32723328, 64, 4)
t715[40]=t49[40] # fslice_write_block(32723328, 64, 4)
t715[41]=t49[41] # fslice_write_block(32723328, 64, 4)
t715[42]=t49[42] # fslice_write_block(32723328, 64, 4)
t715[43]=t49[43] # fslice_write_block(32723328, 64, 4)
t715[44]=t49[44] # fslice_write_block(32723328, 64, 4)
t715[45]=t49[45] # fslice_write_block(32723328, 64, 4)
t715[46]=t49[46] # fslice_write_block(32723328, 64, 4)
t715[47]=t49[47] # fslice_write_block(32723328, 64, 4)
t715[48]=t49[48] # fslice_write_block(32723328, 64, 4)
t715[49]=t49[49] # fslice_write_block(32723328, 64, 4)
t715[50]=t49[50] # fslice_write_block(32723328, 64, 4)
t715[51]=t49[51] # fslice_write_block(32723328, 64, 4)
t715[52]=t49[52] # fslice_write_block(32723328, 64, 4)
t715[53]=t49[53] # fslice_write_block(32723328, 64, 4)
t715[54]=t49[54] # fslice_write_block(32723328, 64, 4)
t715[55]=t49[55] # fslice_write_block(32723328, 64, 4)
t715[56]=t49[56] # fslice_write_block(32723328, 64, 4)
t715[57]=t49[57] # fslice_write_block(32723328, 64, 4)
t715[58]=t49[58] # fslice_write_block(32723328, 64, 4)
t715[59]=t49[59] # fslice_write_block(32723328, 64, 4)
t715[60]=t49[60] # fslice_write_block(32723328, 64, 4)
t715[61]=t49[61] # fslice_write_block(32723328, 64, 4)
t715[62]=t49[62] # fslice_write_block(32723328, 64, 4)
t715[63]=t49[63] # fslice_write_block(32723328, 64, 4)
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
# SSSS Returning back from functionwrite_blocks
# SSSS Returning back from functiontestfs_write_csum
# SSSS Returning back from functiontestfs_put_csum
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 1
ICMP(t599,t673,'ICMP_ULT')
#fslice_value = 1
t716=A("or",t661,t2, 716)
#fslice_value = 0
# SSSS Returning back from functiontestfs_write_data
#fslice_value = 0
# SSSS Returning back from functiontestfs_write_dirent
# SSSS Returning back from functiontestfs_add_dirent
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
#fslice_value = 0
# SSSS Returning back from functiontestfs_create_empty_dir
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
ICMP(t0,t0,'ICMP_UGT')
# testfs_add_dirent()
# SSSS Calling function testfs_add_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
t717=STRLEN(t500)
#fslice_value = 1
t718=A("add",t717,t2, 718)
#fslice_value = 0
t719=N(4, 719)
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t513,t35,'ICMP_EQ')
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
#fslice_value = 0
# testfs_next_dirent()
# SSSS Calling function testfs_next_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t513,t35,'ICMP_EQ')
# testfs_inode_get_size()
# SSSS Calling function testfs_inode_get_size
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_size
ICMP(t1,t521,'ICMP_ULT')
#fslice_value = 8
#fslice_value = 64
#fslice_value = 64
ICMP(t523,t524,'ICMP_UGE')
#fslice_value = 8
# testfs_read_data()
# SSSS Calling function testfs_read_data
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 64
ICMP(t522,t521,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 64
#fslice_value = 0
# testfs_get_block()
# SSSS Calling function testfs_get_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t526,t1,'ICMP_ULT')
#fslice_value = 4
ICMP(t526,t527,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 9:read_blocks()--->testfs_get_block()--->testfs_read_data()--->testfs_next_dirent()--->testfs_add_dirent()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 720
t720=B(64,192,t7,t530, 720) # GetBlock(64, 192) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_get_block
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
#fslice_value = 64
ICMP(t532,t533,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
#DSTRUCT:t720,0:Size|8
#testfs_read_data:buf + buf_offset
#testfs_read_data:block + b_offset
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
# SSSS Returning back from functiontestfs_read_data
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
 #YYY assigned new taint id = 720 taint id checked for = 720
t721=O(t720,721,t720[0],t720[1],t720[2],t720[3]) # Load(140727937608192, 4)
#fslice_value = 0
ICMP(t721,t1,'ICMP_EQ')
#fslice_value = 8
t722=A("add",t15,t721, 722)
t723=M(10, 0, 723,t722)
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
t723[0]=t720[0] # fslice_memmove
t723[1]=t720[1] # fslice_memmove
t723[2]=t720[2] # fslice_memmove
t723[3]=t720[3] # fslice_memmove
t723[4]=t720[4] # fslice_memmove
t723[5]=t720[5] # fslice_memmove
t723[6]=t720[6] # fslice_memmove
t723[7]=t720[7] # fslice_memmove
#DSTRUCT:t720,0:Size|8
#fslice_value = 8
# testfs_read_data()
# SSSS Calling function testfs_read_data
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 64
t724=A("add",t522,t721, 724)
ICMP(t724,t521,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 64
#fslice_value = 0
# testfs_get_block()
# SSSS Calling function testfs_get_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t542,t1,'ICMP_ULT')
#fslice_value = 4
ICMP(t542,t527,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 9:read_blocks()--->testfs_get_block()--->testfs_read_data()--->testfs_next_dirent()--->testfs_add_dirent()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 725
t725=B(64,192,t7,t530, 725) # GetBlock(64, 192) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_get_block
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
t726=A("sub",t721,t1, 726)#SWITCH 721 192
#fslice_value = 64
ICMP(t726,t545,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t723[8]=t725[8] # fslice_memmove
t723[9]=t725[9] # fslice_memmove
#DSTRUCT:t725,8:Size|2
#testfs_read_data:buf + buf_offset
#testfs_read_data:block + b_offset
t727=A("add",t1,t726, 727)
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
# SSSS Returning back from functiontestfs_read_data
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# SSSS Returning back from functiontestfs_next_dirent
#fslice_value = 0
ICMP(t0,t0,'ICMP_EQ')
t728=O(t720,728,t720[4],t720[5],t720[6],t720[7]) # Load(32901012, 4)
#fslice_value = 0
ICMP(t728,t1,'ICMP_ULT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 0
ICMP(t728,t1,'ICMP_ULT')
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
#fslice_value = 0
# testfs_next_dirent()
# SSSS Calling function testfs_next_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t513,t35,'ICMP_EQ')
# testfs_inode_get_size()
# SSSS Calling function testfs_inode_get_size
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_size
ICMP(t724,t521,'ICMP_ULT')
#fslice_value = 8
t729=A("add",t724,t15, 729)
#fslice_value = 64
t730=A("udiv",t729,t7, 730)
#fslice_value = 64
t731=A("sdiv",t724,t7, 731)
ICMP(t730,t731,'ICMP_UGE')
#fslice_value = 8
# testfs_read_data()
# SSSS Calling function testfs_read_data
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 64
t732=A("srem",t724,t7, 732)
ICMP(t729,t521,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
t733=A("add",t724,t1, 733)
#fslice_value = 64
t734=A("sdiv",t733,t7, 734)
#fslice_value = 0
# testfs_get_block()
# SSSS Calling function testfs_get_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t734,t1,'ICMP_ULT')
#fslice_value = 4
ICMP(t734,t527,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 9:read_blocks()--->testfs_get_block()--->testfs_read_data()--->testfs_next_dirent()--->testfs_add_dirent()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 735
t735=B(64,192,t7,t530, 735) # GetBlock(64, 192) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_get_block
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
#fslice_value = 64
t736=A("sub",t7,t732, 736)
ICMP(t532,t736,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t720[0]=t735[10] # fslice_memmove
t720[1]=t735[11] # fslice_memmove
t720[2]=t735[12] # fslice_memmove
t720[3]=t735[13] # fslice_memmove
t720[4]=t735[14] # fslice_memmove
t720[5]=t735[15] # fslice_memmove
t720[6]=t735[16] # fslice_memmove
t720[7]=t735[17] # fslice_memmove
#DSTRUCT:t735,10:Size|8
#testfs_read_data:buf + buf_offset
#testfs_read_data:block + b_offset
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
# SSSS Returning back from functiontestfs_read_data
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
 #YYY assigned new taint id = 735 taint id checked for = 735
t737=O(t735,737,t735[10],t735[11],t735[12],t735[13]) # Load(140727937608192, 4)
#fslice_value = 0
ICMP(t737,t1,'ICMP_EQ')
#fslice_value = 8
t738=A("add",t15,t737, 738)
t739=M(11, 0, 739,t738)
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
t739[0]=t735[10] # fslice_memmove
t739[1]=t735[11] # fslice_memmove
t739[2]=t735[12] # fslice_memmove
t739[3]=t735[13] # fslice_memmove
t739[4]=t735[14] # fslice_memmove
t739[5]=t735[15] # fslice_memmove
t739[6]=t735[16] # fslice_memmove
t739[7]=t735[17] # fslice_memmove
#DSTRUCT:t735,10:Size|8
#fslice_value = 8
# testfs_read_data()
# SSSS Calling function testfs_read_data
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 64
t740=A("srem",t729,t7, 740)
t741=A("add",t729,t737, 741)
ICMP(t741,t521,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
t742=A("add",t729,t1, 742)
#fslice_value = 64
t743=A("sdiv",t742,t7, 743)
#fslice_value = 0
# testfs_get_block()
# SSSS Calling function testfs_get_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t743,t1,'ICMP_ULT')
#fslice_value = 4
ICMP(t743,t527,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 9:read_blocks()--->testfs_get_block()--->testfs_read_data()--->testfs_next_dirent()--->testfs_add_dirent()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 744
t744=B(64,192,t7,t530, 744) # GetBlock(64, 192) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_get_block
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
t745=A("sub",t737,t1, 745)#SWITCH 737 192
#fslice_value = 64
t746=A("sub",t7,t740, 746)
ICMP(t745,t746,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t739[8]=t744[18] # fslice_memmove
t739[9]=t744[19] # fslice_memmove
t739[10]=t744[20] # fslice_memmove
#DSTRUCT:t744,18:Size|3
#testfs_read_data:buf + buf_offset
#testfs_read_data:block + b_offset
t747=A("add",t1,t745, 747)
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
# SSSS Returning back from functiontestfs_read_data
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# SSSS Returning back from functiontestfs_next_dirent
#fslice_value = 0
ICMP(t0,t0,'ICMP_EQ')
t748=O(t735,748,t735[14],t735[15],t735[16],t735[17]) # Load(32903572, 4)
#fslice_value = 0
ICMP(t748,t1,'ICMP_ULT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 0
ICMP(t748,t1,'ICMP_ULT')
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
#fslice_value = 0
# testfs_next_dirent()
# SSSS Calling function testfs_next_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# testfs_inode_get_type()
# SSSS Calling function testfs_inode_get_type
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_type
#fslice_value = 2
ICMP(t513,t35,'ICMP_EQ')
# testfs_inode_get_size()
# SSSS Calling function testfs_inode_get_size
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_size
ICMP(t741,t521,'ICMP_ULT')
# SSSS Returning back from functiontestfs_next_dirent
#fslice_value = 0
ICMP(t0,t0,'ICMP_EQ')
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t1,t1,'ICMP_UGT')
# testfs_inode_get_size()
# SSSS Calling function testfs_inode_get_size
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functiontestfs_inode_get_size
ICMP(t741,t521,'ICMP_EQ')
# testfs_write_dirent()
# SSSS Calling function testfs_write_dirent
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 8
t749=A("add",t15,t718, 749)
#fslice_value = 0
t750=M(12, 0, 750,t749)
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t576,t1,'ICMP_ULT')
t750[8]=t719[0] # fslice_memmove
t750[9]=t719[1] # fslice_memmove
t750[10]=t719[2] # fslice_memmove
t750[11]=t719[3] # fslice_memmove
#DSTRUCT:t719,0:Size|4
#testfs_write_dirent:D_NAME(d)
#testfs_write_dirent:name
t751=A("add",t741,t749, 751)
#fslice_value = 64
t752=A("sdiv",t751,t7, 752)
#fslice_value = 64
t753=A("sdiv",t741,t7, 753)
ICMP(t752,t753,'ICMP_UGE')
# testfs_write_data()
# SSSS Calling function testfs_write_data
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
t754=D(12, 754)
t754[0]=t718[0]
t754[1]=t718[1]
t754[2]=t718[2]
t754[3]=t718[3]
t754[4]=t576[0]
t754[5]=t576[1]
t754[6]=t576[2]
t754[7]=t576[3]
t754[8]=t719[0]
t754[9]=t719[1]
t754[10]=t719[2]
t754[11]=t719[3]
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 64
t755=A("srem",t741,t7, 755)
ICMP(t741,t521,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
t756=A("add",t741,t1, 756)
#fslice_value = 64
t757=A("sdiv",t756,t7, 757)
#fslice_value = 0
# testfs_allocate_block()
# SSSS Calling function testfs_allocate_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t757,t1,'ICMP_ULT')
# testfs_get_block()
# SSSS Calling function testfs_get_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t757,t1,'ICMP_ULT')
#fslice_value = 4
ICMP(t757,t527,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 10:read_blocks()--->testfs_get_block()--->testfs_allocate_block()--->testfs_write_data()--->testfs_write_dirent()--->testfs_add_dirent()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 758
t758=B(64,192,t7,t530, 758) # GetBlock(64, 192) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_get_block
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGT')
# SSSS Returning back from functiontestfs_allocate_block
#fslice_value = 0
#fslice_value = 0
ICMP(t528,t1,'ICMP_ULE')
#fslice_value = 0
ICMP(t528,t1,'ICMP_UGE')
t759=A("sub",t749,t1, 759)
#fslice_value = 64
t760=A("sub",t7,t755, 760)
ICMP(t759,t760,'ICMP_SGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t758[21]=t754[0] # fslice_memmove
t758[22]=t754[1] # fslice_memmove
t758[23]=t754[2] # fslice_memmove
t758[24]=t754[3] # fslice_memmove
t758[25]=t754[4] # fslice_memmove
t758[26]=t754[5] # fslice_memmove
t758[27]=t754[6] # fslice_memmove
t758[28]=t754[7] # fslice_memmove
t758[29]=t754[8] # fslice_memmove
t758[30]=t754[9] # fslice_memmove
t758[31]=t754[10] # fslice_memmove
t758[32]=t754[11] # fslice_memmove
#DSTRUCT:t754,0:Size|12
#testfs_write_data:block + b_offset
#testfs_write_data:buf + buf_offset
#fslice_value = 64
# testfs_calculate_csum()
# SSSS Calling function testfs_calculate_csum
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 4
#fslice_value = 0
ICMP(t615,t1,'ICMP_EQ')
#fslice_value = 4
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t616,'ICMP_ULE')
 #YYY assigned new taint id = 758 taint id checked for = 758
t761=O(t758,761,t758[0],t758[1],t758[2],t758[3]) # Load(140727937605712, 4)
t762=A("xor",t1,t761, 762)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t616,'ICMP_ULE')
 #YYY assigned new taint id = 758 taint id checked for = 758
t763=O(t758,763,t758[4],t758[5],t758[6],t758[7]) # Load(140727937605716, 4)
t764=A("xor",t762,t763, 764)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t42,t616,'ICMP_ULE')
 #YYY assigned new taint id = 758 taint id checked for = 758
t765=O(t758,765,t758[8],t758[9],t758[10],t758[11]) # Load(140727937605720, 4)
t766=A("xor",t764,t765, 766)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t55,t616,'ICMP_ULE')
 #YYY assigned new taint id = 758 taint id checked for = 758
t767=O(t758,767,t758[12],t758[13],t758[14],t758[15]) # Load(140727937605724, 4)
t768=A("xor",t766,t767, 768)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t59,t616,'ICMP_ULE')
 #YYY assigned new taint id = 758 taint id checked for = 758
t769=O(t758,769,t758[16],t758[17],t758[18],t758[19]) # Load(140727937605728, 4)
t770=A("xor",t768,t769, 770)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t63,t616,'ICMP_ULE')
 #XXX assigned new taint id = 758 taint id checked for = 754
t771=O(t758,771,t758[20],t754[0],t754[1],t754[2]) # Load(140727937605732, 4)
t772=A("xor",t770,t771, 772)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t67,t616,'ICMP_ULE')
 #YYY assigned new taint id = 754 taint id checked for = 754
t773=O(t754,773,t754[3],t754[4],t754[5],t754[6]) # Load(140727937605736, 4)
t774=A("xor",t772,t773, 774)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t71,t616,'ICMP_ULE')
 #YYY assigned new taint id = 754 taint id checked for = 754
t775=O(t754,775,t754[7],t754[8],t754[9],t754[10]) # Load(140727937605740, 4)
t776=A("xor",t774,t775, 776)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t75,t616,'ICMP_ULE')
 #XXX assigned new taint id = 754 taint id checked for = 758
t777=O(t754,777,t754[11],t758[33],t758[34],t758[35]) # Load(140727937605744, 4)
t778=A("xor",t776,t777, 778)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t79,t616,'ICMP_ULE')
 #YYY assigned new taint id = 758 taint id checked for = 758
t779=O(t758,779,t758[36],t758[37],t758[38],t758[39]) # Load(140727937605748, 4)
t780=A("xor",t778,t779, 780)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t83,t616,'ICMP_ULE')
 #YYY assigned new taint id = 758 taint id checked for = 758
t781=O(t758,781,t758[40],t758[41],t758[42],t758[43]) # Load(140727937605752, 4)
t782=A("xor",t780,t781, 782)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t87,t616,'ICMP_ULE')
 #YYY assigned new taint id = 758 taint id checked for = 758
t783=O(t758,783,t758[44],t758[45],t758[46],t758[47]) # Load(140727937605756, 4)
t784=A("xor",t782,t783, 784)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t91,t616,'ICMP_ULE')
 #YYY assigned new taint id = 758 taint id checked for = 758
t785=O(t758,785,t758[48],t758[49],t758[50],t758[51]) # Load(140727937605760, 4)
t786=A("xor",t784,t785, 786)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t95,t616,'ICMP_ULE')
 #YYY assigned new taint id = 758 taint id checked for = 758
t787=O(t758,787,t758[52],t758[53],t758[54],t758[55]) # Load(140727937605764, 4)
t788=A("xor",t786,t787, 788)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t99,t616,'ICMP_ULE')
 #YYY assigned new taint id = 758 taint id checked for = 758
t789=O(t758,789,t758[56],t758[57],t758[58],t758[59]) # Load(140727937605768, 4)
t790=A("xor",t788,t789, 790)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t103,t616,'ICMP_ULE')
t791=O(t758,791,t758[60],t758[61],t758[62],t758[63]) # Load(140727937605772, 4)
t792=A("xor",t790,t791, 792)
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
ICMP(t107,t616,'ICMP_ULE')
# SSSS Returning back from functiontestfs_calculate_csum
#fslice_value = 0
#fslice_value = 1
# write_blocks()
# SSSS Calling function write_blocks
# SSSS CALL STACK 8:write_blocks()--->testfs_write_data()--->testfs_write_dirent()--->testfs_add_dirent()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 793
t793=B(64,192,t7,t530, 793) # GetBlock(64, 192) w
t793[0]=t758[0] # fslice_write_block(140727937605712, 64, 192)
t793[1]=t758[1] # fslice_write_block(140727937605712, 64, 192)
t793[2]=t758[2] # fslice_write_block(140727937605712, 64, 192)
t793[3]=t758[3] # fslice_write_block(140727937605712, 64, 192)
t793[4]=t758[4] # fslice_write_block(140727937605712, 64, 192)
t793[5]=t758[5] # fslice_write_block(140727937605712, 64, 192)
t793[6]=t758[6] # fslice_write_block(140727937605712, 64, 192)
t793[7]=t758[7] # fslice_write_block(140727937605712, 64, 192)
t793[8]=t758[8] # fslice_write_block(140727937605712, 64, 192)
t793[9]=t758[9] # fslice_write_block(140727937605712, 64, 192)
t793[10]=t758[10] # fslice_write_block(140727937605712, 64, 192)
t793[11]=t758[11] # fslice_write_block(140727937605712, 64, 192)
t793[12]=t758[12] # fslice_write_block(140727937605712, 64, 192)
t793[13]=t758[13] # fslice_write_block(140727937605712, 64, 192)
t793[14]=t758[14] # fslice_write_block(140727937605712, 64, 192)
t793[15]=t758[15] # fslice_write_block(140727937605712, 64, 192)
t793[16]=t758[16] # fslice_write_block(140727937605712, 64, 192)
t793[17]=t758[17] # fslice_write_block(140727937605712, 64, 192)
t793[18]=t758[18] # fslice_write_block(140727937605712, 64, 192)
t793[19]=t758[19] # fslice_write_block(140727937605712, 64, 192)
t793[20]=t758[20] # fslice_write_block(140727937605712, 64, 192)
t793[21]=t754[0] # fslice_write_block(140727937605712, 64, 192)
t793[22]=t754[1] # fslice_write_block(140727937605712, 64, 192)
t793[23]=t754[2] # fslice_write_block(140727937605712, 64, 192)
t793[24]=t754[3] # fslice_write_block(140727937605712, 64, 192)
t793[25]=t754[4] # fslice_write_block(140727937605712, 64, 192)
t793[26]=t754[5] # fslice_write_block(140727937605712, 64, 192)
t793[27]=t754[6] # fslice_write_block(140727937605712, 64, 192)
t793[28]=t754[7] # fslice_write_block(140727937605712, 64, 192)
t793[29]=t754[8] # fslice_write_block(140727937605712, 64, 192)
t793[30]=t754[9] # fslice_write_block(140727937605712, 64, 192)
t793[31]=t754[10] # fslice_write_block(140727937605712, 64, 192)
t793[32]=t754[11] # fslice_write_block(140727937605712, 64, 192)
t793[33]=t758[33] # fslice_write_block(140727937605712, 64, 192)
t793[34]=t758[34] # fslice_write_block(140727937605712, 64, 192)
t793[35]=t758[35] # fslice_write_block(140727937605712, 64, 192)
t793[36]=t758[36] # fslice_write_block(140727937605712, 64, 192)
t793[37]=t758[37] # fslice_write_block(140727937605712, 64, 192)
t793[38]=t758[38] # fslice_write_block(140727937605712, 64, 192)
t793[39]=t758[39] # fslice_write_block(140727937605712, 64, 192)
t793[40]=t758[40] # fslice_write_block(140727937605712, 64, 192)
t793[41]=t758[41] # fslice_write_block(140727937605712, 64, 192)
t793[42]=t758[42] # fslice_write_block(140727937605712, 64, 192)
t793[43]=t758[43] # fslice_write_block(140727937605712, 64, 192)
t793[44]=t758[44] # fslice_write_block(140727937605712, 64, 192)
t793[45]=t758[45] # fslice_write_block(140727937605712, 64, 192)
t793[46]=t758[46] # fslice_write_block(140727937605712, 64, 192)
t793[47]=t758[47] # fslice_write_block(140727937605712, 64, 192)
t793[48]=t758[48] # fslice_write_block(140727937605712, 64, 192)
t793[49]=t758[49] # fslice_write_block(140727937605712, 64, 192)
t793[50]=t758[50] # fslice_write_block(140727937605712, 64, 192)
t793[51]=t758[51] # fslice_write_block(140727937605712, 64, 192)
t793[52]=t758[52] # fslice_write_block(140727937605712, 64, 192)
t793[53]=t758[53] # fslice_write_block(140727937605712, 64, 192)
t793[54]=t758[54] # fslice_write_block(140727937605712, 64, 192)
t793[55]=t758[55] # fslice_write_block(140727937605712, 64, 192)
t793[56]=t758[56] # fslice_write_block(140727937605712, 64, 192)
t793[57]=t758[57] # fslice_write_block(140727937605712, 64, 192)
t793[58]=t758[58] # fslice_write_block(140727937605712, 64, 192)
t793[59]=t758[59] # fslice_write_block(140727937605712, 64, 192)
t793[60]=t758[60] # fslice_write_block(140727937605712, 64, 192)
t793[61]=t758[61] # fslice_write_block(140727937605712, 64, 192)
t793[62]=t758[62] # fslice_write_block(140727937605712, 64, 192)
t793[63]=t758[63] # fslice_write_block(140727937605712, 64, 192)
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
# SSSS Returning back from functionwrite_blocks
# testfs_put_csum()
# SSSS Calling function testfs_put_csum
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
t794=A("sub",t528,t611, 794)#SWITCH 528 64
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t794,t1,'ICMP_ULT')
#fslice_value = 960
ICMP(t794,t652,'ICMP_ULE')
# testfs_write_csum()
# SSSS Calling function testfs_write_csum
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 4
t795=A("mul",t794,t527, 795)
#fslice_value = 64
t796=A("udiv",t795,t7, 796)
#fslice_value = 64
t797=A("mul",t796,t7, 797)
t798=A("add",t45,t796, 798)#SWITCH 45 0
#fslice_value = 1
# write_blocks()
# SSSS Calling function write_blocks
# SSSS CALL STACK 10:write_blocks()--->testfs_write_csum()--->testfs_put_csum()--->testfs_write_data()--->testfs_write_dirent()--->testfs_add_dirent()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t799=A("mul",t798,t7, 799)
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
t800=A("add",t798,t1, 800)
#fslice_value = 64
#gBlockTAINT 801
t801=B(64,4,t7,t800, 801) # GetBlock(64, 4) w
t801[0]=t792[0] # fslice_write_block(32723328, 64, 4)
t801[1]=t792[1] # fslice_write_block(32723328, 64, 4)
t801[2]=t792[2] # fslice_write_block(32723328, 64, 4)
t801[3]=t792[3] # fslice_write_block(32723328, 64, 4)
t801[4]=t713[0] # fslice_write_block(32723328, 64, 4)
t801[5]=t713[1] # fslice_write_block(32723328, 64, 4)
t801[6]=t713[2] # fslice_write_block(32723328, 64, 4)
t801[7]=t713[3] # fslice_write_block(32723328, 64, 4)
t801[8]=t49[8] # fslice_write_block(32723328, 64, 4)
t801[9]=t49[9] # fslice_write_block(32723328, 64, 4)
t801[10]=t49[10] # fslice_write_block(32723328, 64, 4)
t801[11]=t49[11] # fslice_write_block(32723328, 64, 4)
t801[12]=t49[12] # fslice_write_block(32723328, 64, 4)
t801[13]=t49[13] # fslice_write_block(32723328, 64, 4)
t801[14]=t49[14] # fslice_write_block(32723328, 64, 4)
t801[15]=t49[15] # fslice_write_block(32723328, 64, 4)
t801[16]=t49[16] # fslice_write_block(32723328, 64, 4)
t801[17]=t49[17] # fslice_write_block(32723328, 64, 4)
t801[18]=t49[18] # fslice_write_block(32723328, 64, 4)
t801[19]=t49[19] # fslice_write_block(32723328, 64, 4)
t801[20]=t49[20] # fslice_write_block(32723328, 64, 4)
t801[21]=t49[21] # fslice_write_block(32723328, 64, 4)
t801[22]=t49[22] # fslice_write_block(32723328, 64, 4)
t801[23]=t49[23] # fslice_write_block(32723328, 64, 4)
t801[24]=t49[24] # fslice_write_block(32723328, 64, 4)
t801[25]=t49[25] # fslice_write_block(32723328, 64, 4)
t801[26]=t49[26] # fslice_write_block(32723328, 64, 4)
t801[27]=t49[27] # fslice_write_block(32723328, 64, 4)
t801[28]=t49[28] # fslice_write_block(32723328, 64, 4)
t801[29]=t49[29] # fslice_write_block(32723328, 64, 4)
t801[30]=t49[30] # fslice_write_block(32723328, 64, 4)
t801[31]=t49[31] # fslice_write_block(32723328, 64, 4)
t801[32]=t49[32] # fslice_write_block(32723328, 64, 4)
t801[33]=t49[33] # fslice_write_block(32723328, 64, 4)
t801[34]=t49[34] # fslice_write_block(32723328, 64, 4)
t801[35]=t49[35] # fslice_write_block(32723328, 64, 4)
t801[36]=t49[36] # fslice_write_block(32723328, 64, 4)
t801[37]=t49[37] # fslice_write_block(32723328, 64, 4)
t801[38]=t49[38] # fslice_write_block(32723328, 64, 4)
t801[39]=t49[39] # fslice_write_block(32723328, 64, 4)
t801[40]=t49[40] # fslice_write_block(32723328, 64, 4)
t801[41]=t49[41] # fslice_write_block(32723328, 64, 4)
t801[42]=t49[42] # fslice_write_block(32723328, 64, 4)
t801[43]=t49[43] # fslice_write_block(32723328, 64, 4)
t801[44]=t49[44] # fslice_write_block(32723328, 64, 4)
t801[45]=t49[45] # fslice_write_block(32723328, 64, 4)
t801[46]=t49[46] # fslice_write_block(32723328, 64, 4)
t801[47]=t49[47] # fslice_write_block(32723328, 64, 4)
t801[48]=t49[48] # fslice_write_block(32723328, 64, 4)
t801[49]=t49[49] # fslice_write_block(32723328, 64, 4)
t801[50]=t49[50] # fslice_write_block(32723328, 64, 4)
t801[51]=t49[51] # fslice_write_block(32723328, 64, 4)
t801[52]=t49[52] # fslice_write_block(32723328, 64, 4)
t801[53]=t49[53] # fslice_write_block(32723328, 64, 4)
t801[54]=t49[54] # fslice_write_block(32723328, 64, 4)
t801[55]=t49[55] # fslice_write_block(32723328, 64, 4)
t801[56]=t49[56] # fslice_write_block(32723328, 64, 4)
t801[57]=t49[57] # fslice_write_block(32723328, 64, 4)
t801[58]=t49[58] # fslice_write_block(32723328, 64, 4)
t801[59]=t49[59] # fslice_write_block(32723328, 64, 4)
t801[60]=t49[60] # fslice_write_block(32723328, 64, 4)
t801[61]=t49[61] # fslice_write_block(32723328, 64, 4)
t801[62]=t49[62] # fslice_write_block(32723328, 64, 4)
t801[63]=t49[63] # fslice_write_block(32723328, 64, 4)
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
# SSSS Returning back from functionwrite_blocks
# SSSS Returning back from functiontestfs_write_csum
# SSSS Returning back from functiontestfs_put_csum
t802=A("add",t1,t759, 802)
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t2,t1,'ICMP_UGT')
#fslice_value = 1
ICMP(t521,t751,'ICMP_ULT')
#fslice_value = 1
#fslice_value = 0
# SSSS Returning back from functiontestfs_write_data
#fslice_value = 0
# SSSS Returning back from functiontestfs_write_dirent
# SSSS Returning back from functiontestfs_add_dirent
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# testfs_sync_inode()
# SSSS Calling function testfs_sync_inode
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t803=A("and",t593,t2, 803)
#fslice_value = 0
ICMP(t803,t1,'ICMP_UGT')
# testfs_read_inode_block()
# SSSS Calling function testfs_read_inode_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
# testfs_inode_to_block_nr()
# SSSS Calling function testfs_inode_to_block_nr
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2
#fslice_value = 0
#fslice_value = 0
ICMP(t489,t1,'ICMP_ULT')
#fslice_value = 128
ICMP(t489,t490,'ICMP_ULE')
# SSSS Returning back from functiontestfs_inode_to_block_nr
#fslice_value = 0
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 7:read_blocks()--->testfs_read_inode_block()--->testfs_sync_inode()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 804
t804=B(64,64,t7,t494, 804) # GetBlock(64, 64) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_read_inode_block
# testfs_inode_to_block_offset()
# SSSS Calling function testfs_inode_to_block_offset
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2
#fslice_value = 32
#fslice_value = 0
#fslice_value = 0
ICMP(t497,t1,'ICMP_ULT')
#fslice_value = 64
ICMP(t497,t7,'ICMP_ULE')
# SSSS Returning back from functiontestfs_inode_to_block_offset
#fslice_value = 0
t804[0]=t495[0] # fslice_memmove
t804[1]=t495[1] # fslice_memmove
t804[2]=t495[2] # fslice_memmove
t804[3]=t495[3] # fslice_memmove
t804[4]=t751[0] # fslice_memmove
t804[5]=t751[1] # fslice_memmove
t804[6]=t751[2] # fslice_memmove
t804[7]=t751[3] # fslice_memmove
t804[8]=t495[8] # fslice_memmove
t804[9]=t495[9] # fslice_memmove
t804[10]=t495[10] # fslice_memmove
t804[11]=t495[11] # fslice_memmove
t804[12]=t495[12] # fslice_memmove
t804[13]=t495[13] # fslice_memmove
t804[14]=t495[14] # fslice_memmove
t804[15]=t495[15] # fslice_memmove
t804[16]=t495[16] # fslice_memmove
t804[17]=t495[17] # fslice_memmove
t804[18]=t495[18] # fslice_memmove
t804[19]=t495[19] # fslice_memmove
t804[20]=t495[20] # fslice_memmove
t804[21]=t495[21] # fslice_memmove
t804[22]=t495[22] # fslice_memmove
t804[23]=t495[23] # fslice_memmove
t804[24]=t495[24] # fslice_memmove
t804[25]=t495[25] # fslice_memmove
t804[26]=t495[26] # fslice_memmove
t804[27]=t495[27] # fslice_memmove
t804[28]=t495[28] # fslice_memmove
t804[29]=t495[29] # fslice_memmove
t804[30]=t495[30] # fslice_memmove
t804[31]=t495[31] # fslice_memmove
#DSTRUCT:t495,0:Size|32
#testfs_sync_inode:block + block_offset
#testfs_sync_inode:&in->in
# testfs_write_inode_block()
# SSSS Calling function testfs_write_inode_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
# testfs_inode_to_block_nr()
# SSSS Calling function testfs_inode_to_block_nr
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2
#fslice_value = 0
#fslice_value = 0
ICMP(t489,t1,'ICMP_ULT')
#fslice_value = 128
ICMP(t489,t490,'ICMP_ULE')
# SSSS Returning back from functiontestfs_inode_to_block_nr
#fslice_value = 0
#fslice_value = 1
# write_blocks()
# SSSS Calling function write_blocks
# SSSS CALL STACK 7:write_blocks()--->testfs_write_inode_block()--->testfs_sync_inode()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 805
t805=B(64,64,t7,t494, 805) # GetBlock(64, 64) w
t805[0]=t495[0] # fslice_write_block(140727937611472, 64, 64)
t805[1]=t495[1] # fslice_write_block(140727937611472, 64, 64)
t805[2]=t495[2] # fslice_write_block(140727937611472, 64, 64)
t805[3]=t495[3] # fslice_write_block(140727937611472, 64, 64)
t805[4]=t751[0] # fslice_write_block(140727937611472, 64, 64)
t805[5]=t751[1] # fslice_write_block(140727937611472, 64, 64)
t805[6]=t751[2] # fslice_write_block(140727937611472, 64, 64)
t805[7]=t751[3] # fslice_write_block(140727937611472, 64, 64)
t805[8]=t495[8] # fslice_write_block(140727937611472, 64, 64)
t805[9]=t495[9] # fslice_write_block(140727937611472, 64, 64)
t805[10]=t495[10] # fslice_write_block(140727937611472, 64, 64)
t805[11]=t495[11] # fslice_write_block(140727937611472, 64, 64)
t805[12]=t495[12] # fslice_write_block(140727937611472, 64, 64)
t805[13]=t495[13] # fslice_write_block(140727937611472, 64, 64)
t805[14]=t495[14] # fslice_write_block(140727937611472, 64, 64)
t805[15]=t495[15] # fslice_write_block(140727937611472, 64, 64)
t805[16]=t495[16] # fslice_write_block(140727937611472, 64, 64)
t805[17]=t495[17] # fslice_write_block(140727937611472, 64, 64)
t805[18]=t495[18] # fslice_write_block(140727937611472, 64, 64)
t805[19]=t495[19] # fslice_write_block(140727937611472, 64, 64)
t805[20]=t495[20] # fslice_write_block(140727937611472, 64, 64)
t805[21]=t495[21] # fslice_write_block(140727937611472, 64, 64)
t805[22]=t495[22] # fslice_write_block(140727937611472, 64, 64)
t805[23]=t495[23] # fslice_write_block(140727937611472, 64, 64)
t805[24]=t495[24] # fslice_write_block(140727937611472, 64, 64)
t805[25]=t495[25] # fslice_write_block(140727937611472, 64, 64)
t805[26]=t495[26] # fslice_write_block(140727937611472, 64, 64)
t805[27]=t495[27] # fslice_write_block(140727937611472, 64, 64)
t805[28]=t495[28] # fslice_write_block(140727937611472, 64, 64)
t805[29]=t495[29] # fslice_write_block(140727937611472, 64, 64)
t805[30]=t495[30] # fslice_write_block(140727937611472, 64, 64)
t805[31]=t495[31] # fslice_write_block(140727937611472, 64, 64)
t805[32]=t804[32] # fslice_write_block(140727937611472, 64, 64)
t805[33]=t804[33] # fslice_write_block(140727937611472, 64, 64)
t805[34]=t804[34] # fslice_write_block(140727937611472, 64, 64)
t805[35]=t804[35] # fslice_write_block(140727937611472, 64, 64)
t805[36]=t804[36] # fslice_write_block(140727937611472, 64, 64)
t805[37]=t804[37] # fslice_write_block(140727937611472, 64, 64)
t805[38]=t804[38] # fslice_write_block(140727937611472, 64, 64)
t805[39]=t804[39] # fslice_write_block(140727937611472, 64, 64)
t805[40]=t804[40] # fslice_write_block(140727937611472, 64, 64)
t805[41]=t804[41] # fslice_write_block(140727937611472, 64, 64)
t805[42]=t804[42] # fslice_write_block(140727937611472, 64, 64)
t805[43]=t804[43] # fslice_write_block(140727937611472, 64, 64)
t805[44]=t804[44] # fslice_write_block(140727937611472, 64, 64)
t805[45]=t804[45] # fslice_write_block(140727937611472, 64, 64)
t805[46]=t804[46] # fslice_write_block(140727937611472, 64, 64)
t805[47]=t804[47] # fslice_write_block(140727937611472, 64, 64)
t805[48]=t804[48] # fslice_write_block(140727937611472, 64, 64)
t805[49]=t804[49] # fslice_write_block(140727937611472, 64, 64)
t805[50]=t804[50] # fslice_write_block(140727937611472, 64, 64)
t805[51]=t804[51] # fslice_write_block(140727937611472, 64, 64)
t805[52]=t804[52] # fslice_write_block(140727937611472, 64, 64)
t805[53]=t804[53] # fslice_write_block(140727937611472, 64, 64)
t805[54]=t804[54] # fslice_write_block(140727937611472, 64, 64)
t805[55]=t804[55] # fslice_write_block(140727937611472, 64, 64)
t805[56]=t804[56] # fslice_write_block(140727937611472, 64, 64)
t805[57]=t804[57] # fslice_write_block(140727937611472, 64, 64)
t805[58]=t804[58] # fslice_write_block(140727937611472, 64, 64)
t805[59]=t804[59] # fslice_write_block(140727937611472, 64, 64)
t805[60]=t804[60] # fslice_write_block(140727937611472, 64, 64)
t805[61]=t804[61] # fslice_write_block(140727937611472, 64, 64)
t805[62]=t804[62] # fslice_write_block(140727937611472, 64, 64)
t805[63]=t804[63] # fslice_write_block(140727937611472, 64, 64)
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
# SSSS Returning back from functionwrite_blocks
# SSSS Returning back from functiontestfs_write_inode_block
#fslice_value = 4294967294
t806=A("and",t593,t520, 806)
# SSSS Returning back from functiontestfs_sync_inode
# testfs_sync_inode()
# SSSS Calling function testfs_sync_inode
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t807=A("and",t716,t2, 807)
#fslice_value = 0
ICMP(t807,t1,'ICMP_UGT')
# testfs_read_inode_block()
# SSSS Calling function testfs_read_inode_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
# testfs_inode_to_block_nr()
# SSSS Calling function testfs_inode_to_block_nr
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2
#fslice_value = 0
#fslice_value = 0
ICMP(t586,t1,'ICMP_ULT')
#fslice_value = 128
ICMP(t586,t490,'ICMP_ULE')
# SSSS Returning back from functiontestfs_inode_to_block_nr
#fslice_value = 0
#fslice_value = 1
# read_blocks()
# SSSS Calling function read_blocks
# SSSS CALL STACK 7:read_blocks()--->testfs_read_inode_block()--->testfs_sync_inode()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 808
t808=B(64,64,t7,t589, 808) # GetBlock(64, 64) r
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
# SSSS Returning back from functionread_blocks
# SSSS Returning back from functiontestfs_read_inode_block
# testfs_inode_to_block_offset()
# SSSS Calling function testfs_inode_to_block_offset
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2
#fslice_value = 32
#fslice_value = 0
#fslice_value = 0
ICMP(t592,t1,'ICMP_ULT')
#fslice_value = 64
ICMP(t592,t7,'ICMP_ULE')
# SSSS Returning back from functiontestfs_inode_to_block_offset
#fslice_value = 0
t808[32]=t35[0] # fslice_memmove
t808[33]=t35[1] # fslice_memmove
t808[34]=t35[2] # fslice_memmove
t808[35]=t35[3] # fslice_memmove
t808[36]=t673[0] # fslice_memmove
t808[37]=t673[1] # fslice_memmove
t808[38]=t673[2] # fslice_memmove
t808[39]=t673[3] # fslice_memmove
t808[40]=t590[40] # fslice_memmove
t808[41]=t590[41] # fslice_memmove
t808[42]=t590[42] # fslice_memmove
t808[43]=t590[43] # fslice_memmove
t808[44]=t612[0] # fslice_memmove
t808[45]=t612[1] # fslice_memmove
t808[46]=t612[2] # fslice_memmove
t808[47]=t612[3] # fslice_memmove
t808[48]=t590[48] # fslice_memmove
t808[49]=t590[49] # fslice_memmove
t808[50]=t590[50] # fslice_memmove
t808[51]=t590[51] # fslice_memmove
t808[52]=t590[52] # fslice_memmove
t808[53]=t590[53] # fslice_memmove
t808[54]=t590[54] # fslice_memmove
t808[55]=t590[55] # fslice_memmove
t808[56]=t590[56] # fslice_memmove
t808[57]=t590[57] # fslice_memmove
t808[58]=t590[58] # fslice_memmove
t808[59]=t590[59] # fslice_memmove
t808[60]=t590[60] # fslice_memmove
t808[61]=t590[61] # fslice_memmove
t808[62]=t590[62] # fslice_memmove
t808[63]=t590[63] # fslice_memmove
#DSTRUCT:t35,0:Size|32
#testfs_sync_inode:block + block_offset
#testfs_sync_inode:&in->in
# testfs_write_inode_block()
# SSSS Calling function testfs_write_inode_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
# testfs_inode_to_block_nr()
# SSSS Calling function testfs_inode_to_block_nr
#fslice_value = 0
#fslice_value = 0
#fslice_value = 2
#fslice_value = 0
#fslice_value = 0
ICMP(t586,t1,'ICMP_ULT')
#fslice_value = 128
ICMP(t586,t490,'ICMP_ULE')
# SSSS Returning back from functiontestfs_inode_to_block_nr
#fslice_value = 0
#fslice_value = 1
# write_blocks()
# SSSS Calling function write_blocks
# SSSS CALL STACK 7:write_blocks()--->testfs_write_inode_block()--->testfs_sync_inode()--->testfs_create_file_or_dir()--->cmd_mkdir()--->handle_command()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 809
t809=B(64,64,t7,t589, 809) # GetBlock(64, 64) w
t809[0]=t808[0] # fslice_write_block(140727937611472, 64, 64)
t809[1]=t808[1] # fslice_write_block(140727937611472, 64, 64)
t809[2]=t808[2] # fslice_write_block(140727937611472, 64, 64)
t809[3]=t808[3] # fslice_write_block(140727937611472, 64, 64)
t809[4]=t808[4] # fslice_write_block(140727937611472, 64, 64)
t809[5]=t808[5] # fslice_write_block(140727937611472, 64, 64)
t809[6]=t808[6] # fslice_write_block(140727937611472, 64, 64)
t809[7]=t808[7] # fslice_write_block(140727937611472, 64, 64)
t809[8]=t808[8] # fslice_write_block(140727937611472, 64, 64)
t809[9]=t808[9] # fslice_write_block(140727937611472, 64, 64)
t809[10]=t808[10] # fslice_write_block(140727937611472, 64, 64)
t809[11]=t808[11] # fslice_write_block(140727937611472, 64, 64)
t809[12]=t808[12] # fslice_write_block(140727937611472, 64, 64)
t809[13]=t808[13] # fslice_write_block(140727937611472, 64, 64)
t809[14]=t808[14] # fslice_write_block(140727937611472, 64, 64)
t809[15]=t808[15] # fslice_write_block(140727937611472, 64, 64)
t809[16]=t808[16] # fslice_write_block(140727937611472, 64, 64)
t809[17]=t808[17] # fslice_write_block(140727937611472, 64, 64)
t809[18]=t808[18] # fslice_write_block(140727937611472, 64, 64)
t809[19]=t808[19] # fslice_write_block(140727937611472, 64, 64)
t809[20]=t808[20] # fslice_write_block(140727937611472, 64, 64)
t809[21]=t808[21] # fslice_write_block(140727937611472, 64, 64)
t809[22]=t808[22] # fslice_write_block(140727937611472, 64, 64)
t809[23]=t808[23] # fslice_write_block(140727937611472, 64, 64)
t809[24]=t808[24] # fslice_write_block(140727937611472, 64, 64)
t809[25]=t808[25] # fslice_write_block(140727937611472, 64, 64)
t809[26]=t808[26] # fslice_write_block(140727937611472, 64, 64)
t809[27]=t808[27] # fslice_write_block(140727937611472, 64, 64)
t809[28]=t808[28] # fslice_write_block(140727937611472, 64, 64)
t809[29]=t808[29] # fslice_write_block(140727937611472, 64, 64)
t809[30]=t808[30] # fslice_write_block(140727937611472, 64, 64)
t809[31]=t808[31] # fslice_write_block(140727937611472, 64, 64)
t809[32]=t35[0] # fslice_write_block(140727937611472, 64, 64)
t809[33]=t35[1] # fslice_write_block(140727937611472, 64, 64)
t809[34]=t35[2] # fslice_write_block(140727937611472, 64, 64)
t809[35]=t35[3] # fslice_write_block(140727937611472, 64, 64)
t809[36]=t673[0] # fslice_write_block(140727937611472, 64, 64)
t809[37]=t673[1] # fslice_write_block(140727937611472, 64, 64)
t809[38]=t673[2] # fslice_write_block(140727937611472, 64, 64)
t809[39]=t673[3] # fslice_write_block(140727937611472, 64, 64)
t809[40]=t590[40] # fslice_write_block(140727937611472, 64, 64)
t809[41]=t590[41] # fslice_write_block(140727937611472, 64, 64)
t809[42]=t590[42] # fslice_write_block(140727937611472, 64, 64)
t809[43]=t590[43] # fslice_write_block(140727937611472, 64, 64)
t809[44]=t612[0] # fslice_write_block(140727937611472, 64, 64)
t809[45]=t612[1] # fslice_write_block(140727937611472, 64, 64)
t809[46]=t612[2] # fslice_write_block(140727937611472, 64, 64)
t809[47]=t612[3] # fslice_write_block(140727937611472, 64, 64)
t809[48]=t590[48] # fslice_write_block(140727937611472, 64, 64)
t809[49]=t590[49] # fslice_write_block(140727937611472, 64, 64)
t809[50]=t590[50] # fslice_write_block(140727937611472, 64, 64)
t809[51]=t590[51] # fslice_write_block(140727937611472, 64, 64)
t809[52]=t590[52] # fslice_write_block(140727937611472, 64, 64)
t809[53]=t590[53] # fslice_write_block(140727937611472, 64, 64)
t809[54]=t590[54] # fslice_write_block(140727937611472, 64, 64)
t809[55]=t590[55] # fslice_write_block(140727937611472, 64, 64)
t809[56]=t590[56] # fslice_write_block(140727937611472, 64, 64)
t809[57]=t590[57] # fslice_write_block(140727937611472, 64, 64)
t809[58]=t590[58] # fslice_write_block(140727937611472, 64, 64)
t809[59]=t590[59] # fslice_write_block(140727937611472, 64, 64)
t809[60]=t590[60] # fslice_write_block(140727937611472, 64, 64)
t809[61]=t590[61] # fslice_write_block(140727937611472, 64, 64)
t809[62]=t590[62] # fslice_write_block(140727937611472, 64, 64)
t809[63]=t590[63] # fslice_write_block(140727937611472, 64, 64)
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
# SSSS Returning back from functionwrite_blocks
# SSSS Returning back from functiontestfs_write_inode_block
#fslice_value = 4294967294
t810=A("and",t716,t520, 810)
# SSSS Returning back from functiontestfs_sync_inode
# testfs_put_inode()
# SSSS Calling function testfs_put_inode
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t811=A("and",t810,t2, 811)
#fslice_value = 0
ICMP(t811,t1,'ICMP_EQ')
#fslice_value = 4294967295
t812=A("add",t2,t504, 812)
#fslice_value = 0
ICMP(t812,t1,'ICMP_EQ')
# inode_hash_remove()
# SSSS Calling function inode_hash_remove
#fslice_value = 0
#fslice_value = 0
# hlist_del()
# SSSS Calling function hlist_del
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# INIT_HLIST_NODE()
# SSSS Calling function INIT_HLIST_NODE
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functionINIT_HLIST_NODE
# SSSS Returning back from functionhlist_del
# SSSS Returning back from functioninode_hash_remove
# SSSS Returning back from functiontestfs_put_inode
#fslice_value = 2
# testfs_tx_commit()
# SSSS Calling function testfs_tx_commit
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t35,t35,'ICMP_EQ')
#fslice_value = 0
# SSSS Returning back from functiontestfs_tx_commit
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t507,t1,'ICMP_UGE')
#fslice_value = 0
# SSSS Returning back from functiontestfs_create_file_or_dir
# SSSS Returning back from functioncmd_mkdir
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# SSSS Returning back from functionhandle_command
#fslice_value = 0
#fslice_value = 18446744073709551615
ICMP(t0,t498,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
# handle_command()
# SSSS Calling function handle_command
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_EQ')
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 1
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
ICMP(t0,t1,'ICMP_EQ')
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
ICMP(t11,t0,'ICMP_ULE')
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 5
ICMP(t42,t499,'ICMP_SGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 5
ICMP(t55,t499,'ICMP_SGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 5
ICMP(t59,t499,'ICMP_SGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 5
ICMP(t63,t499,'ICMP_SGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 5
ICMP(t67,t499,'ICMP_SGT')
# cmd_quit()
# SSSS Calling function cmd_quit
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
#fslice_value = 0
# SSSS Returning back from functioncmd_quit
#fslice_value = 0
ICMP(t1,t1,'ICMP_ULE')
# SSSS Returning back from functionhandle_command
# testfs_put_inode()
# SSSS Calling function testfs_put_inode
#fslice_value = 0
#fslice_value = 0
#fslice_value = 1
t813=A("and",t806,t2, 813)
#fslice_value = 0
ICMP(t813,t1,'ICMP_EQ')
#fslice_value = 4294967295
#fslice_value = 0
ICMP(t812,t1,'ICMP_EQ')
# inode_hash_remove()
# SSSS Calling function inode_hash_remove
#fslice_value = 0
#fslice_value = 0
# hlist_del()
# SSSS Calling function hlist_del
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
# INIT_HLIST_NODE()
# SSSS Calling function INIT_HLIST_NODE
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functionINIT_HLIST_NODE
# SSSS Returning back from functionhlist_del
# SSSS Returning back from functioninode_hash_remove
# SSSS Returning back from functiontestfs_put_inode
# testfs_close_super_block()
# SSSS Calling function testfs_close_super_block
#fslice_value = 0
#fslice_value = 0
#fslice_value = 4
# testfs_tx_start()
# SSSS Calling function testfs_tx_start
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t1,'ICMP_EQ')
# SSSS Returning back from functiontestfs_tx_start
# testfs_write_super_block()
# SSSS Calling function testfs_write_super_block
#fslice_value = 0
#fslice_value = 0
#XXX Assigning new Taint
t814=S(28, 814)
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
# XXX Destination address taint Id is 0
#DSTRUCT:t814,0:Size|28
#testfs_write_super_block:block
#testfs_write_super_block:&sb->sb
#fslice_value = 0
#fslice_value = 1
# write_blocks()
# SSSS Calling function write_blocks
# SSSS CALL STACK 4:write_blocks()--->testfs_write_super_block()--->testfs_close_super_block()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
#fslice_value = 64
#gBlockTAINT 815
t815=B(64,0,t7,t9, 815) # GetBlock(64, 0) w
t815[0]=t814[0] # fslice_write_block(140727937618096, 64, 0)
t815[1]=t814[1] # fslice_write_block(140727937618096, 64, 0)
t815[2]=t814[2] # fslice_write_block(140727937618096, 64, 0)
t815[3]=t814[3] # fslice_write_block(140727937618096, 64, 0)
t815[4]=t814[4] # fslice_write_block(140727937618096, 64, 0)
t815[5]=t814[5] # fslice_write_block(140727937618096, 64, 0)
t815[6]=t814[6] # fslice_write_block(140727937618096, 64, 0)
t815[7]=t814[7] # fslice_write_block(140727937618096, 64, 0)
t815[8]=t814[8] # fslice_write_block(140727937618096, 64, 0)
t815[9]=t814[9] # fslice_write_block(140727937618096, 64, 0)
t815[10]=t814[10] # fslice_write_block(140727937618096, 64, 0)
t815[11]=t814[11] # fslice_write_block(140727937618096, 64, 0)
t815[12]=t814[12] # fslice_write_block(140727937618096, 64, 0)
t815[13]=t814[13] # fslice_write_block(140727937618096, 64, 0)
t815[14]=t814[14] # fslice_write_block(140727937618096, 64, 0)
t815[15]=t814[15] # fslice_write_block(140727937618096, 64, 0)
t815[16]=t814[16] # fslice_write_block(140727937618096, 64, 0)
t815[17]=t814[17] # fslice_write_block(140727937618096, 64, 0)
t815[18]=t814[18] # fslice_write_block(140727937618096, 64, 0)
t815[19]=t814[19] # fslice_write_block(140727937618096, 64, 0)
t815[20]=t814[20] # fslice_write_block(140727937618096, 64, 0)
t815[21]=t814[21] # fslice_write_block(140727937618096, 64, 0)
t815[22]=t814[22] # fslice_write_block(140727937618096, 64, 0)
t815[23]=t814[23] # fslice_write_block(140727937618096, 64, 0)
t815[24]=t814[24] # fslice_write_block(140727937618096, 64, 0)
t815[25]=t814[25] # fslice_write_block(140727937618096, 64, 0)
t815[26]=t814[26] # fslice_write_block(140727937618096, 64, 0)
t815[27]=t814[27] # fslice_write_block(140727937618096, 64, 0)
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618124] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618125] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618126] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618127] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618128] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618129] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618130] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618131] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618132] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618133] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618134] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618135] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618136] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618137] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618138] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618139] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618140] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618141] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618142] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618143] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618144] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618145] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618146] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618147] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618148] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618149] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618150] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618151] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618152] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618153] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618154] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618155] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618156] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618157] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618158] does not contain a taint value!
# __fslice_write_block(140727937618096, 64, 0)::gShadow[140727937618159] does not contain a taint value!
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
# SSSS Returning back from functionwrite_blocks
# SSSS Returning back from functiontestfs_write_super_block
# inode_hash_destroy()
# SSSS Calling function inode_hash_destroy
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
#fslice_value = 256
ICMP(t1,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t11,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t42,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t55,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t59,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t63,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t67,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t71,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t75,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t79,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t83,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t87,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t91,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t95,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t99,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t103,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t107,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t111,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t115,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t119,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t123,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t127,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t131,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t135,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t139,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t143,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t147,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t151,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t155,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t159,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t163,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t167,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t171,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t175,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t179,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t183,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t187,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t191,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t195,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t199,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t203,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t207,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t211,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t215,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t219,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t223,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t227,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t231,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t235,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t239,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t243,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t247,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t251,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t255,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t259,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t263,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t267,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t271,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t275,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t279,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t283,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t287,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t288,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t289,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t290,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t291,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t292,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t293,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t294,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t295,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t296,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t297,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t298,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t299,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t300,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t301,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t302,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t303,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t304,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t305,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t306,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t307,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t308,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t309,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t310,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t311,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t312,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t313,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t314,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t315,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t316,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t317,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t318,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t319,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t320,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t321,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t322,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t323,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t324,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t325,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t326,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t327,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t328,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t329,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t330,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t331,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t332,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t333,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t334,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t335,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t336,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t337,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t338,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t339,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t340,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t341,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t342,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t343,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t344,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t345,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t346,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t347,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t348,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t349,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t350,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t351,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t352,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t353,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t354,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t355,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t356,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t357,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t358,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t359,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t360,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t361,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t362,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t363,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t364,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t365,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t366,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t367,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t368,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t369,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t370,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t371,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t372,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t373,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t374,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t375,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t376,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t377,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t378,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t379,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t380,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t381,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t382,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t383,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t384,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t385,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t386,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t387,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t388,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t389,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t390,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t391,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t392,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t393,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t394,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t395,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t396,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t397,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t398,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t399,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t400,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t401,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t402,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t403,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t404,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t405,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t406,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t407,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t408,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t409,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t410,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t411,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t412,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t413,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t414,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t415,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t416,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t417,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t418,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t419,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t420,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t421,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t422,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t423,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t424,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t425,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t426,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t427,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t428,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t429,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t430,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t431,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t432,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t433,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t434,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t435,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t436,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t437,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t438,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t439,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t440,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t441,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t442,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t443,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t444,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t445,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t446,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t447,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t448,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t449,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t450,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t451,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t452,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t453,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t454,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t455,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t456,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t457,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t458,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t459,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t460,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t461,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t462,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t463,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t464,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t465,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t466,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t467,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t468,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t469,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t470,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t471,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t472,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t473,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t474,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t475,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t476,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t477,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t478,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t479,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t480,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t481,t286,'ICMP_ULE')
# hlist_empty()
# SSSS Calling function hlist_empty
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t0,'ICMP_UGT')
#fslice_value = 1
# SSSS Returning back from functionhlist_empty
#fslice_value = 0
ICMP(t535,t1,'ICMP_UGT')
#fslice_value = 1
#fslice_value = 0
#fslice_value = 256
ICMP(t482,t286,'ICMP_ULE')
# SSSS Returning back from functioninode_hash_destroy
ICMP(t0,t0,'ICMP_UGT')
# bitmap_getdata()
# SSSS Calling function bitmap_getdata
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functionbitmap_getdata
 #YYY assigned new taint id = 814 taint id checked for = 814
t816=O(t814,816,t814[0],t814[1],t814[2],t814[3]) # Load(32700640, 4)
#fslice_value = 1
# write_blocks()
# SSSS Calling function write_blocks
# SSSS CALL STACK 3:write_blocks()--->testfs_close_super_block()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t817=A("mul",t816,t7, 817)
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t2,'ICMP_ULE')
#fslice_value = 64
t818=A("add",t816,t1, 818)
#fslice_value = 64
#gBlockTAINT 819
t819=B(64,1,t7,t818, 819) # GetBlock(64, 1) w
t819[0]=t574[0] # fslice_write_block(32711568, 64, 1)
t819[1]=t25[1] # fslice_write_block(32711568, 64, 1)
t819[2]=t25[2] # fslice_write_block(32711568, 64, 1)
t819[3]=t25[3] # fslice_write_block(32711568, 64, 1)
t819[4]=t25[4] # fslice_write_block(32711568, 64, 1)
t819[5]=t25[5] # fslice_write_block(32711568, 64, 1)
t819[6]=t25[6] # fslice_write_block(32711568, 64, 1)
t819[7]=t25[7] # fslice_write_block(32711568, 64, 1)
t819[8]=t25[8] # fslice_write_block(32711568, 64, 1)
t819[9]=t25[9] # fslice_write_block(32711568, 64, 1)
t819[10]=t25[10] # fslice_write_block(32711568, 64, 1)
t819[11]=t25[11] # fslice_write_block(32711568, 64, 1)
t819[12]=t25[12] # fslice_write_block(32711568, 64, 1)
t819[13]=t25[13] # fslice_write_block(32711568, 64, 1)
t819[14]=t25[14] # fslice_write_block(32711568, 64, 1)
t819[15]=t25[15] # fslice_write_block(32711568, 64, 1)
t819[16]=t25[16] # fslice_write_block(32711568, 64, 1)
t819[17]=t25[17] # fslice_write_block(32711568, 64, 1)
t819[18]=t25[18] # fslice_write_block(32711568, 64, 1)
t819[19]=t25[19] # fslice_write_block(32711568, 64, 1)
t819[20]=t25[20] # fslice_write_block(32711568, 64, 1)
t819[21]=t25[21] # fslice_write_block(32711568, 64, 1)
t819[22]=t25[22] # fslice_write_block(32711568, 64, 1)
t819[23]=t25[23] # fslice_write_block(32711568, 64, 1)
t819[24]=t25[24] # fslice_write_block(32711568, 64, 1)
t819[25]=t25[25] # fslice_write_block(32711568, 64, 1)
t819[26]=t25[26] # fslice_write_block(32711568, 64, 1)
t819[27]=t25[27] # fslice_write_block(32711568, 64, 1)
t819[28]=t25[28] # fslice_write_block(32711568, 64, 1)
t819[29]=t25[29] # fslice_write_block(32711568, 64, 1)
t819[30]=t25[30] # fslice_write_block(32711568, 64, 1)
t819[31]=t25[31] # fslice_write_block(32711568, 64, 1)
t819[32]=t25[32] # fslice_write_block(32711568, 64, 1)
t819[33]=t25[33] # fslice_write_block(32711568, 64, 1)
t819[34]=t25[34] # fslice_write_block(32711568, 64, 1)
t819[35]=t25[35] # fslice_write_block(32711568, 64, 1)
t819[36]=t25[36] # fslice_write_block(32711568, 64, 1)
t819[37]=t25[37] # fslice_write_block(32711568, 64, 1)
t819[38]=t25[38] # fslice_write_block(32711568, 64, 1)
t819[39]=t25[39] # fslice_write_block(32711568, 64, 1)
t819[40]=t25[40] # fslice_write_block(32711568, 64, 1)
t819[41]=t25[41] # fslice_write_block(32711568, 64, 1)
t819[42]=t25[42] # fslice_write_block(32711568, 64, 1)
t819[43]=t25[43] # fslice_write_block(32711568, 64, 1)
t819[44]=t25[44] # fslice_write_block(32711568, 64, 1)
t819[45]=t25[45] # fslice_write_block(32711568, 64, 1)
t819[46]=t25[46] # fslice_write_block(32711568, 64, 1)
t819[47]=t25[47] # fslice_write_block(32711568, 64, 1)
t819[48]=t25[48] # fslice_write_block(32711568, 64, 1)
t819[49]=t25[49] # fslice_write_block(32711568, 64, 1)
t819[50]=t25[50] # fslice_write_block(32711568, 64, 1)
t819[51]=t25[51] # fslice_write_block(32711568, 64, 1)
t819[52]=t25[52] # fslice_write_block(32711568, 64, 1)
t819[53]=t25[53] # fslice_write_block(32711568, 64, 1)
t819[54]=t25[54] # fslice_write_block(32711568, 64, 1)
t819[55]=t25[55] # fslice_write_block(32711568, 64, 1)
t819[56]=t25[56] # fslice_write_block(32711568, 64, 1)
t819[57]=t25[57] # fslice_write_block(32711568, 64, 1)
t819[58]=t25[58] # fslice_write_block(32711568, 64, 1)
t819[59]=t25[59] # fslice_write_block(32711568, 64, 1)
t819[60]=t25[60] # fslice_write_block(32711568, 64, 1)
t819[61]=t25[61] # fslice_write_block(32711568, 64, 1)
t819[62]=t25[62] # fslice_write_block(32711568, 64, 1)
t819[63]=t25[63] # fslice_write_block(32711568, 64, 1)
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t2,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t2,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
# SSSS Returning back from functionwrite_blocks
# bitmap_destroy()
# SSSS Calling function bitmap_destroy
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functionbitmap_destroy
ICMP(t0,t0,'ICMP_UGT')
# bitmap_getdata()
# SSSS Calling function bitmap_getdata
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functionbitmap_getdata
 #YYY assigned new taint id = 814 taint id checked for = 814
t820=O(t814,820,t814[4],t814[5],t814[6],t814[7]) # Load(32700644, 4)
#fslice_value = 2
# write_blocks()
# SSSS Calling function write_blocks
# SSSS CALL STACK 3:write_blocks()--->testfs_close_super_block()--->main()--->
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 64
t821=A("mul",t820,t7, 821)
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
#fslice_value = 0
#fslice_value = 0
ICMP(t1,t35,'ICMP_ULE')
#fslice_value = 64
t822=A("add",t820,t1, 822)
#fslice_value = 64
#gBlockTAINT 823
t823=B(64,2,t7,t822, 823) # GetBlock(64, 2) w
t823[0]=t606[0] # fslice_write_block(32714832, 64, 2)
t823[1]=t38[1] # fslice_write_block(32714832, 64, 2)
t823[2]=t38[2] # fslice_write_block(32714832, 64, 2)
t823[3]=t38[3] # fslice_write_block(32714832, 64, 2)
t823[4]=t38[4] # fslice_write_block(32714832, 64, 2)
t823[5]=t38[5] # fslice_write_block(32714832, 64, 2)
t823[6]=t38[6] # fslice_write_block(32714832, 64, 2)
t823[7]=t38[7] # fslice_write_block(32714832, 64, 2)
t823[8]=t38[8] # fslice_write_block(32714832, 64, 2)
t823[9]=t38[9] # fslice_write_block(32714832, 64, 2)
t823[10]=t38[10] # fslice_write_block(32714832, 64, 2)
t823[11]=t38[11] # fslice_write_block(32714832, 64, 2)
t823[12]=t38[12] # fslice_write_block(32714832, 64, 2)
t823[13]=t38[13] # fslice_write_block(32714832, 64, 2)
t823[14]=t38[14] # fslice_write_block(32714832, 64, 2)
t823[15]=t38[15] # fslice_write_block(32714832, 64, 2)
t823[16]=t38[16] # fslice_write_block(32714832, 64, 2)
t823[17]=t38[17] # fslice_write_block(32714832, 64, 2)
t823[18]=t38[18] # fslice_write_block(32714832, 64, 2)
t823[19]=t38[19] # fslice_write_block(32714832, 64, 2)
t823[20]=t38[20] # fslice_write_block(32714832, 64, 2)
t823[21]=t38[21] # fslice_write_block(32714832, 64, 2)
t823[22]=t38[22] # fslice_write_block(32714832, 64, 2)
t823[23]=t38[23] # fslice_write_block(32714832, 64, 2)
t823[24]=t38[24] # fslice_write_block(32714832, 64, 2)
t823[25]=t38[25] # fslice_write_block(32714832, 64, 2)
t823[26]=t38[26] # fslice_write_block(32714832, 64, 2)
t823[27]=t38[27] # fslice_write_block(32714832, 64, 2)
t823[28]=t38[28] # fslice_write_block(32714832, 64, 2)
t823[29]=t38[29] # fslice_write_block(32714832, 64, 2)
t823[30]=t38[30] # fslice_write_block(32714832, 64, 2)
t823[31]=t38[31] # fslice_write_block(32714832, 64, 2)
t823[32]=t38[32] # fslice_write_block(32714832, 64, 2)
t823[33]=t38[33] # fslice_write_block(32714832, 64, 2)
t823[34]=t38[34] # fslice_write_block(32714832, 64, 2)
t823[35]=t38[35] # fslice_write_block(32714832, 64, 2)
t823[36]=t38[36] # fslice_write_block(32714832, 64, 2)
t823[37]=t38[37] # fslice_write_block(32714832, 64, 2)
t823[38]=t38[38] # fslice_write_block(32714832, 64, 2)
t823[39]=t38[39] # fslice_write_block(32714832, 64, 2)
t823[40]=t38[40] # fslice_write_block(32714832, 64, 2)
t823[41]=t38[41] # fslice_write_block(32714832, 64, 2)
t823[42]=t38[42] # fslice_write_block(32714832, 64, 2)
t823[43]=t38[43] # fslice_write_block(32714832, 64, 2)
t823[44]=t38[44] # fslice_write_block(32714832, 64, 2)
t823[45]=t38[45] # fslice_write_block(32714832, 64, 2)
t823[46]=t38[46] # fslice_write_block(32714832, 64, 2)
t823[47]=t38[47] # fslice_write_block(32714832, 64, 2)
t823[48]=t38[48] # fslice_write_block(32714832, 64, 2)
t823[49]=t38[49] # fslice_write_block(32714832, 64, 2)
t823[50]=t38[50] # fslice_write_block(32714832, 64, 2)
t823[51]=t38[51] # fslice_write_block(32714832, 64, 2)
t823[52]=t38[52] # fslice_write_block(32714832, 64, 2)
t823[53]=t38[53] # fslice_write_block(32714832, 64, 2)
t823[54]=t38[54] # fslice_write_block(32714832, 64, 2)
t823[55]=t38[55] # fslice_write_block(32714832, 64, 2)
t823[56]=t38[56] # fslice_write_block(32714832, 64, 2)
t823[57]=t38[57] # fslice_write_block(32714832, 64, 2)
t823[58]=t38[58] # fslice_write_block(32714832, 64, 2)
t823[59]=t38[59] # fslice_write_block(32714832, 64, 2)
t823[60]=t38[60] # fslice_write_block(32714832, 64, 2)
t823[61]=t38[61] # fslice_write_block(32714832, 64, 2)
t823[62]=t38[62] # fslice_write_block(32714832, 64, 2)
t823[63]=t38[63] # fslice_write_block(32714832, 64, 2)
#fslice_value = 1
#fslice_value = 0
ICMP(t11,t35,'ICMP_ULE')
#fslice_value = 64
t824=A("add",t820,t11, 824)
#fslice_value = 64
#gBlockTAINT 825
t825=B(64,3,t7,t824, 825) # GetBlock(64, 3) w
t825[0]=t41[0] # fslice_write_block(32714896, 64, 3)
t825[1]=t41[1] # fslice_write_block(32714896, 64, 3)
t825[2]=t41[2] # fslice_write_block(32714896, 64, 3)
t825[3]=t41[3] # fslice_write_block(32714896, 64, 3)
t825[4]=t41[4] # fslice_write_block(32714896, 64, 3)
t825[5]=t41[5] # fslice_write_block(32714896, 64, 3)
t825[6]=t41[6] # fslice_write_block(32714896, 64, 3)
t825[7]=t41[7] # fslice_write_block(32714896, 64, 3)
t825[8]=t41[8] # fslice_write_block(32714896, 64, 3)
t825[9]=t41[9] # fslice_write_block(32714896, 64, 3)
t825[10]=t41[10] # fslice_write_block(32714896, 64, 3)
t825[11]=t41[11] # fslice_write_block(32714896, 64, 3)
t825[12]=t41[12] # fslice_write_block(32714896, 64, 3)
t825[13]=t41[13] # fslice_write_block(32714896, 64, 3)
t825[14]=t41[14] # fslice_write_block(32714896, 64, 3)
t825[15]=t41[15] # fslice_write_block(32714896, 64, 3)
t825[16]=t41[16] # fslice_write_block(32714896, 64, 3)
t825[17]=t41[17] # fslice_write_block(32714896, 64, 3)
t825[18]=t41[18] # fslice_write_block(32714896, 64, 3)
t825[19]=t41[19] # fslice_write_block(32714896, 64, 3)
t825[20]=t41[20] # fslice_write_block(32714896, 64, 3)
t825[21]=t41[21] # fslice_write_block(32714896, 64, 3)
t825[22]=t41[22] # fslice_write_block(32714896, 64, 3)
t825[23]=t41[23] # fslice_write_block(32714896, 64, 3)
t825[24]=t41[24] # fslice_write_block(32714896, 64, 3)
t825[25]=t41[25] # fslice_write_block(32714896, 64, 3)
t825[26]=t41[26] # fslice_write_block(32714896, 64, 3)
t825[27]=t41[27] # fslice_write_block(32714896, 64, 3)
t825[28]=t41[28] # fslice_write_block(32714896, 64, 3)
t825[29]=t41[29] # fslice_write_block(32714896, 64, 3)
t825[30]=t41[30] # fslice_write_block(32714896, 64, 3)
t825[31]=t41[31] # fslice_write_block(32714896, 64, 3)
t825[32]=t41[32] # fslice_write_block(32714896, 64, 3)
t825[33]=t41[33] # fslice_write_block(32714896, 64, 3)
t825[34]=t41[34] # fslice_write_block(32714896, 64, 3)
t825[35]=t41[35] # fslice_write_block(32714896, 64, 3)
t825[36]=t41[36] # fslice_write_block(32714896, 64, 3)
t825[37]=t41[37] # fslice_write_block(32714896, 64, 3)
t825[38]=t41[38] # fslice_write_block(32714896, 64, 3)
t825[39]=t41[39] # fslice_write_block(32714896, 64, 3)
t825[40]=t41[40] # fslice_write_block(32714896, 64, 3)
t825[41]=t41[41] # fslice_write_block(32714896, 64, 3)
t825[42]=t41[42] # fslice_write_block(32714896, 64, 3)
t825[43]=t41[43] # fslice_write_block(32714896, 64, 3)
t825[44]=t41[44] # fslice_write_block(32714896, 64, 3)
t825[45]=t41[45] # fslice_write_block(32714896, 64, 3)
t825[46]=t41[46] # fslice_write_block(32714896, 64, 3)
t825[47]=t41[47] # fslice_write_block(32714896, 64, 3)
t825[48]=t41[48] # fslice_write_block(32714896, 64, 3)
t825[49]=t41[49] # fslice_write_block(32714896, 64, 3)
t825[50]=t41[50] # fslice_write_block(32714896, 64, 3)
t825[51]=t41[51] # fslice_write_block(32714896, 64, 3)
t825[52]=t41[52] # fslice_write_block(32714896, 64, 3)
t825[53]=t41[53] # fslice_write_block(32714896, 64, 3)
t825[54]=t41[54] # fslice_write_block(32714896, 64, 3)
t825[55]=t41[55] # fslice_write_block(32714896, 64, 3)
t825[56]=t41[56] # fslice_write_block(32714896, 64, 3)
t825[57]=t41[57] # fslice_write_block(32714896, 64, 3)
t825[58]=t41[58] # fslice_write_block(32714896, 64, 3)
t825[59]=t41[59] # fslice_write_block(32714896, 64, 3)
t825[60]=t41[60] # fslice_write_block(32714896, 64, 3)
t825[61]=t41[61] # fslice_write_block(32714896, 64, 3)
t825[62]=t41[62] # fslice_write_block(32714896, 64, 3)
t825[63]=t41[63] # fslice_write_block(32714896, 64, 3)
#fslice_value = 1
#fslice_value = 0
ICMP(t42,t35,'ICMP_ULE')
#fslice_value = 64
ICMP(t0,t35,'ICMP_UGT')
#fslice_value = 0
#fslice_value = 0
ICMP(t0,t1,'ICMP_ULE')
# SSSS Returning back from functionwrite_blocks
# bitmap_destroy()
# SSSS Calling function bitmap_destroy
#fslice_value = 0
#fslice_value = 0
# SSSS Returning back from functionbitmap_destroy
#fslice_value = 4
# testfs_tx_commit()
# SSSS Calling function testfs_tx_commit
#fslice_value = 0
#fslice_value = 0
#fslice_value = 0
ICMP(t527,t527,'ICMP_EQ')
#fslice_value = 0
# SSSS Returning back from functiontestfs_tx_commit
# SSSS Returning back from functiontestfs_close_super_block
#fslice_value = 0
# SSSS Returning back from functionmain
