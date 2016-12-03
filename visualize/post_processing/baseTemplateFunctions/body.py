removeConstants=False
# main()
t1=V(0, 1) # Taint<1, 0, 0>
# parse_arguments()
t2=V(1, 2) # Taint<2, 0, 0>
# testfs_init_super_block()
# read_blocks()
t7=V(64, 7) # Taint<7, 0, 0>
t9=A("add",t1,t1, 9)
t10=B(64,0,t7,t9, 10) # GetBlock(64, 0) r
t11=A("add",t1,t2, 11)
# bitmap_create()
# bitmap_getdata()
# read_blocks()
# bitmap_create()
# bitmap_getdata()
# read_blocks()
t42=A("add",t11,t2, 42)
t45=O(t10,45,t10[8],t10[9],t10[10],t10[11]) # Load(27047064, 4)
# read_blocks()
t55=A("add",t42,t2, 55)
t59=A("add",t55,t2, 59)
t63=A("add",t59,t2, 63)
t65=A("add",t45,t63, 65)#SWITCH 45 0
t66=B(64,9,t7,t65, 66) # GetBlock(64, 9) r
