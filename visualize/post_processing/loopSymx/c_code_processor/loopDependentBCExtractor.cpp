/* The program takes a linux indented *.c file and prints only those functions that have a for (, 
 * do { or a while ( condition in them */

#include <fstream>
#include <sstream>
#include <string>
#include <iostream>
#include <map>
#include <cassert>

void printStats(char *fname, int fCount, int loopCount, int seqLoop, int nestedLoop, int ldvOp, int ldcvOp)
{
	std::cerr << "FileName = " << fname << std::endl;
	std::cerr << "Function Count = " << fCount << std::endl;	
	std::cerr << "Loop Count = " << loopCount << std::endl;	
	std::cerr << "Seq Loop Count = " << seqLoop << std::endl;
	std::cerr << "Nested Loop Count = " << nestedLoop << std::endl;
	std::cerr << "Loop Dependent Variable Op = " << ldvOp << std::endl;
	std::cerr << "Loop Dependent Conditional Variable Op = " << ldcvOp << std::endl;
}

// only looks at first few spaces

std::string trim(std::string str)
{
	size_t startpos = str.find_first_not_of(" \t");
	if( std::string::npos != startpos )
	{
	    str = str.substr( startpos );
	}
	return str;
}

// looks at declaration * variable and removes variable
// returns abc

std::string removeDecl(std::string str)
{
	if(str.find(" ") == std::string::npos){
		return str;	
	}
	std::string resstr = str;
	while(resstr.find(" ") != std::string::npos)
	{
		resstr = resstr.substr(1, resstr.size());
	}
	if(resstr.size() == 0){
		return str;
	}

//return resstr;
	std::string removestar = resstr;
	if(removestar.find("*") != std::string::npos) 
	{
		while(removestar[0] == '*'){
			removestar = removestar.substr(1, removestar.size());
		}
	}
	return removestar;
}

std::string getFirst(std::string line, std::string operation)
{
	std::string trimmedLine = trim(line);
	std::string::size_type pos = trimmedLine.find(" =");
	if(pos == std::string::npos){
		std::cerr << "WARNING COULD NOT FIND FIRST TOKEN IN LINE " << line;
		return std::string();
	}
	trimmedLine.erase( trimmedLine.begin() + pos, trimmedLine.end());
//	return trimmedLine.substr(0, pos);

//	return trimmedLine;
	std::string lastToken = removeDecl(trimmedLine);
	return lastToken;// trimmedLine.substr(lastToken, pos);
}

std::string getSecond(std::string line, std::string operation)
{
	std::string trimmedLine = trim(line);
	std::string::size_type pos = trimmedLine.find(" =");
	if(pos == std::string::npos){
		std::cerr << "WARNING COULD NOT FIND FIRST TOKEN IN LINE " << line;
		return std::string();
	}
	return trimmedLine.substr(pos,line.length());
}


void processForLDBC(std::map <std::string, std::string > ldvOp, std::map <std::string, std::string > ldcvOp, char * fileName,
			int *ldvbCount1, int *ldcvbCount1)
{
	std::ifstream infile(fileName);
	std::string line;
	int ldvbCount = 0;
	int ldcvbCount = 1;
	while (std::getline(infile, line)){
		for( std::map <std::string , std::string>:: iterator it = ldvOp.begin() ; it != ldvOp.end() ; it++){
			std::string operation = it->first;
			if(operation.size() == 0){
				std::cerr << "OPSIZE IS 0" << std::endl;
				continue;
			}
			if ( (line.find(operation) != std::string::npos) && 
			(( line.find("if (") != std::string::npos) || (line.find("switch") != std::string::npos))){
				ldvbCount++;
				std::cerr << " USAGE OF " << it->first << std::endl;
				std::cerr << " IN LINE " << line << std::endl;
			}
		}	
	}
	std::ifstream infile2(fileName);

	while (std::getline(infile2, line)){
		for( std::map <std::string , std::string>:: iterator it = ldvOp.begin() ; it != ldvOp.end() ; it++){
			std::string operation = it->first;
			if(operation.size() == 0){
				std::cerr << "OPSIZE IS 0" << std::endl;
				continue;
			}
			if ( (line.find(operation) != std::string::npos) && 
			(( line.find("if (") != std::string::npos) || (line.find("switch") != std::string::npos))){
				ldcvbCount++;
			}
		}	
	}
	
	std::cerr<< "FILE: " << " ldvbCount = " << ldvbCount << std::endl;
	std::cerr<< "FILE: " << " ldcvbCount = " << ldcvbCount << std::endl;
	*ldvbCount1 = ldvbCount;
	*ldcvbCount1 = ldcvbCount;
}

int main(int argc, char *argv[])
{
	int i;
	int totalFunctionCount = 0;
	int totalLoopCount = 0;
	int totalSeqLoopCount = 0;
	int totalNestedLoopCount = 0;
	int totalLDVCount = 0;
	int totalLDCVCount = 0;
	int totalLDVBCount = 0;
	int totalLDCVBCount = 0;

	for (i = 1 ; i < argc; i++){
		std::ifstream infile(argv[i]);
		std::string outfilename (std::string(argv[i]) + ".out");
		std::fstream outfile;
		outfile.open(outfilename.c_str(), std::fstream::out | std::fstream::app);
		std::string line;
		std::string functionBody;
		bool lineAppend = false;
		bool containsLoop = false;
		bool containsBranchAndLoop = false;
		// loop dependent variable Operation
		std::map <std::string, std::string > ldvOp;	// for() { x = 10 }  . ldvOp.insert(x , 10)
		// conditional loop dependent variable Operation
		std::map <std::string, std::string > ldcvOp; 	// for() { if () { x = 10 } } . ldcvOp.insert(x , 10)
		std::string prevline;
		std::string prevprevline;
		int functionCount = 0;
		int loopBracket = 0;
		int ifBracket = 0;
		int loopCount = 0;
		int seqLoop = 0;
		int nestedLoop = 0;
		bool bracketTurn = false;	// false = loop bracket. true = if bracket
		while (std::getline(infile, line))
		{
			if(loopBracket > 0){
				if(line.find("if (") != std::string::npos && 
					line.find("{") != std::string::npos){
				// XXX DOES NOT HANDLE SINGLE IF STATEMENTS
					ifBracket++;
				}
	//			std::cerr << "LOOP BODY " << line << std::endl;
				if(line.find("{") != std::string::npos){ 
					if(line.find("if (") == std::string::npos){
						loopBracket++;
					}else{
						ifBracket++;
					}
				}
				if(line.find("}") != std::string::npos){
					if(ifBracket == 0){
						loopBracket--;
					}else{
						ifBracket--;
					}
				}
				
				if(line.find(" = ") != std::string::npos){
					std::string Operand = getFirst(line," = ");
					std::string Operation = getSecond(line," = ");
					if(ifBracket == 0){
						ldvOp[Operand] = Operation;
					} else {
						ldcvOp[Operand] = Operation;
					}
				}
				else if(line.find("++") != std::string::npos){
					std::string Operand = getFirst(line,"++");
					if(ifBracket == 0){
						ldvOp[Operand] = std::string("add1");
					} else {
						ldcvOp[Operand] = std::string("add1");
					}
				}
				else if(line.find("--") != std::string::npos){
					std::string Operand = getFirst(line,"--");
					if(ifBracket == 0){
						ldvOp[Operand] = std::string("sub1");
					} else {
						ldcvOp[Operand] = std::string("sub1");
					}
				}else if(line.find("+-") != std::string::npos){
					std::string Operand = getFirst(line,"+=");
					std::string Operation = getSecond(line,"+=");
					if(ifBracket == 0){
						ldvOp[Operand] = std::string("+=") + Operation;
					} else {
						ldcvOp[Operand] = std::string("+=") + Operation;
					}
				}else if(line.find("-=") != std::string::npos){
					std::string Operand = getFirst(line,"-=");
					std::string Operation = getSecond(line,"-=");

					if(ifBracket == 0){
						ldvOp[Operand] = std::string("-=") + Operation;
					} else {
						ldcvOp[Operand] = std::string("-=") + Operation;
					}
				}
			}
			if(lineAppend == true){
				functionBody += line;
				functionBody += "\n";
			}
			if(line.find("do {")!=std::string::npos || line.find("while (")!= std::string::npos || 
				line.find("for (") != std::string::npos){
				//std::cerr << " FOUND LOOP CONSTRUCT " << std::endl;
				containsLoop = true;
//				std::cerr << "LOOP BEGIN AT LINE " << line << std::endl;
				loopCount++;
				if(loopBracket == 0){
			//		std::cerr << "LOOP BODY" << line << std::endl;
					loopBracket++;
					seqLoop++;
				}else{
					nestedLoop++;
				}
			}
			if(!line.compare("{")){	// Function BEGIN
			//	std::cerr << " FOUND FUNCTION START " << std::endl;
				lineAppend = true;
				functionBody += prevprevline;
				functionBody += "\n";
				functionBody += prevline;
				functionBody += "\n";
				functionBody += line;
				functionBody += "\n";
			}
			else if(!line.compare("}")){	// Function END
			//	std::cerr << " FOUND FUNCTION END " << std::endl;
				lineAppend = false;
				if(containsBranchAndLoop){
					outfile << functionBody ;
				}
				containsBranchAndLoop = false;
				containsLoop = false;
				functionBody.clear();
				functionCount++;
			}
			prevprevline = prevline;
			prevline = line;
			
	    	}	// file end
		printStats(argv[i],functionCount, loopCount, seqLoop, nestedLoop, ldvOp.size(), ldcvOp.size()); 
				
		totalFunctionCount += functionCount;
		totalLoopCount += loopCount;
		totalSeqLoopCount += seqLoop;
		totalNestedLoopCount += nestedLoop;
		totalLDVCount  += ldvOp.size();
		totalLDCVCount += ldcvOp.size();

		int ldvbCount, ldcvbCount;		
		processForLDBC(ldvOp, ldcvOp, argv[i], &ldvbCount, &ldcvbCount);
		if(ldvbCount <= ldvOp.size()){
			std::cerr << "ldvbCount = " << ldvbCount << std::endl;
			std::cerr << "ldvOp.size = " << ldvOp.size() << std::endl;
			assert(ldvbCount <= ldvOp.size());
		}
//		if(ldcvOp.size() > 0)
//			assert(ldcvbCount <= ldcvOp.size());
		totalLDVBCount += ldvbCount;
		totalLDCVBCount += ldcvbCount;
	}
	// end of all files
	std::cerr << "====== SUMMARY ======" << std::endl;
	std::cerr << "total Function Count = " << totalFunctionCount << std::endl;
	std::cerr << "total Loop Count = " << totalLoopCount << std::endl;
	std::cerr << "total Sequential Loop Count = " << totalSeqLoopCount << std::endl;
	std::cerr << "total Nested Loop Count = " << totalNestedLoopCount << std::endl;	
	std::cerr << "total LDV Count = " << totalLDVCount << std::endl;
	std::cerr << "total LDCV Count = " << totalLDCVCount << std::endl;	
	std::cerr << "total LDBC Count = " << totalLDVBCount << std::endl;
	std::cerr << "total LDCV Count = " << totalLDCVBCount << std::endl;	
}
