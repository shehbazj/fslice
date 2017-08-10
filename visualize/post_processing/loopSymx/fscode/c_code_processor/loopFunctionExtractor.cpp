/* The program takes a linux indented *.c file and prints only those functions that have a for (, 
 * do { or a while ( condition in them */

#include <fstream>
#include <sstream>
#include <string>
#include <iostream>

int main(int argc, char *argv[])
{
	int i;
	for (i = 1 ; i < argc; i++){
		std::ifstream infile(argv[i]);
		std::string outfilename (std::string(argv[i]) + ".out");
		std::fstream outfile;
		outfile.open(outfilename.c_str(), std::fstream::out | std::fstream::app);
		std::string line;
		std::string functionBody;
		bool lineAppend = false;
		bool printFunction = false;
		std::string prevline;
		std::string prevprevline;
		while (std::getline(infile, line))
		{
			if(lineAppend == true){
				functionBody += line;
				functionBody += "\n";
			}
			if(line.find("do {")!=std::string::npos || line.find("while (")!= std::string::npos || 
				line.find("for (") != std::string::npos){
				//std::cerr << " FOUND LOOP CONSTRUCT " << std::endl;
				printFunction = true;
			}
			if(!line.compare("{")){
			//	std::cerr << " FOUND FUNCTION START " << std::endl;
				lineAppend = true;
				functionBody += prevprevline;
				functionBody += "\n";
				functionBody += prevline;
				functionBody += "\n";
				functionBody += line;
				functionBody += "\n";
			}
			else if(!line.compare("}")){
			//	std::cerr << " FOUND FUNCTION END " << std::endl;
				lineAppend = false;
				if(printFunction){
					outfile << functionBody ;
					printFunction = false;
				}
				functionBody.clear();
			}
			prevprevline = prevline;
			prevline = line;
	    	}
	}
}
