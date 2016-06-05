import itertools
import sys

labelId = 0
removeConstants = None

def num_to_taint_object(str):
	return getattr(sys.modules[__name__], str)


def V( a, b):
	return a;

def operate(op, op1, op2):
	if op is "add":
		return op1 + op2
	elif op is "mul":
		return op1 * op2
	elif op is "sdiv":
		return op1 / op2
	elif op is "udiv":
		return op1 / op2
	else:
		print "Undefined Binary Operation"

def generateLabel(op,op1,op2):
	global labelId
	labelId+=1
	label = "L"+str(labelId)
	if removeConstants is True:
		if isinstance(op1,int):
			op1 = 'C'
		if isinstance(op2,int):
			op2 = 'C'
	print label,op,op1,op2
	return label

def A( op, op1, op2, discard):
	global labelId
	if isinstance(op1,int) and isinstance(op2,int):
		return operate(op, op1, op2)

	elif isinstance(op1,basestring) and isinstance(op2,int):
		if op2 == 0:
			#print op1
			return op1
		return generateLabel(op,op1,op2)

	elif ((isinstance(op1,basestring) and isinstance(op2,list)) or
	(isinstance(op1,list) and isinstance(op2,basestring)) or
	(isinstance(op1,list) and isinstance(op2,list))):
		return generateLabel(op,op1,op2)
		
	elif isinstance(op1,list) and isinstance(op2, int):
		#if op2 == 0:
		#	print "returning ",op1
		#	return op1
		#print op,op1,op2
		mylist = []
		mylist.append(op)
		mylist.append('B')
		mylist.append(op1[-1])  # add block number
		mylist.append(op1[0])	# add block start
		mylist.append(op1[-2])	# add block end
		if removeConstants is True:
			mylist.append('C')
		else:
			mylist.append(op2)	# add op2
		labelId+=1
		label = "L" + str(labelId)
		print label,mylist
		return label
	else:
		print "No case matched for",op,op1,op2
		return []

# returns list containing all indexes block number and block taint

def B( bsize, bnum, bsizeTaint, bnumTaint, discard):
	#print 'B [',str(bnum),']'
	mylist = []
	for i in range(0,bsize):
		mylist.append(i)
	mylist.append(bnum)
	#print mylist
	print "B"+str(bnum),bnumTaint
	return mylist

# returns list of indexes and block number

def O(*arg):
	mylist = []
	for name in range(2,len(arg)):
		mylist.append(arg[name])
	mylist.append((arg[0])[-1])	# append block number
	return mylist

if __name__ == "__main__":
    """ Main Start """

removeConstants=True
# main()
t1=V(0, 1) # Taint<1, 0, 0>
# parse_arguments()
t2=V(1, 2) # Taint<2, 0, 0>
# testfs_init_super_block()
t4=V(64, 4) # Taint<4, 0, 0>
# read_blocks()
t8=A("add",t1,t1, 8)
t9=B(64,0,t4,t8, 9) # GetBlock(64, 0)
t10=A("add",t1,t2, 10)
# read_blocks()
t41=A("add",t10,t2, 41)
t44=O(t9,44,t9[8],t9[9],t9[10],t9[11]) # Load(13557976, 4)
# read_blocks()
t54=A("add",t41,t2, 54)
t58=A("add",t54,t2, 58)
t62=A("add",t58,t2, 62)
t66=A("add",t62,t2, 66)
t70=A("add",t66,t2, 70)
t74=A("add",t70,t2, 74)
t78=A("add",t74,t2, 78)
t82=A("add",t78,t2, 82)
t86=A("add",t82,t2, 86)
t90=A("add",t86,t2, 90)
t94=A("add",t90,t2, 94)
t98=A("add",t94,t2, 98)
t102=A("add",t98,t2, 102)
t106=A("add",t102,t2, 106)
t110=A("add",t106,t2, 110)
t114=A("add",t110,t2, 114)
t118=A("add",t114,t2, 118)
t122=A("add",t118,t2, 122)
t126=A("add",t122,t2, 126)
t130=A("add",t126,t2, 130)
t134=A("add",t130,t2, 134)
t138=A("add",t134,t2, 138)
t142=A("add",t138,t2, 142)
t146=A("add",t142,t2, 146)
t150=A("add",t146,t2, 150)
t154=A("add",t150,t2, 154)
t156=A("add",t44,t154, 156)
t157=B(64,32,t4,t156, 157) # GetBlock(64, 32)
