import argparse
import re

if __name__ == "__main__":
    """ Main Start """

    parser = argparse.ArgumentParser()
    parser.add_argument('taint_val', type=str, help="TaintID to trace: ex. 1234")
    parser.add_argument('trace_file', type=str, help="The path to the trace file.")
    parser.add_argument('-d', type=int, help='The maximum depth (optional)')
    parser.add_argument('-b', action='store_true')
    args = parser.parse_args()

    with open(args.trace_file, 'r') as f:

        current_depth = 0
        taint_str = None
        input_lines = None
        relevant_lines = []
        printFunctionNames = None
        # printFunctionNames = True

        if args.b:
            # Backward pass
            taint_str = 't' + args.taint_val + '='
            input_lines = reversed(f.readlines())
        else:
            # Forward pass
            taint_str = 't' + args.taint_val
            input_lines = f.readlines()

        relevant = set([taint_str])
        for line in input_lines:
            if line[0] == '#' and not printFunctionNames:
                continue

            # Match
            line = line.strip()
            if args.b:
                curset = set(re.findall(r"t[0-9]+=", line))
            else:
                curset = set(re.findall(r"t[0-9]+", line))

            if len(curset) and relevant.intersection(curset):
                cur = re.findall(r"t[0-9]+", line)
                sol = []

                for taint in cur:
                    if args.b:
                        sol.append(taint + '=')
                    else:
                        sol.append(taint)

                relevant |= set(sol)
                relevant_lines.append(line)

                # Increase the current depth.
                current_depth += 1

            if printFunctionNames:
                if line.endswith("()"):
                    relevant_lines.append(line)

            # Check if the maximum depth is reached.
            if args.d and current_depth > args.d:
                break

        for line in relevant_lines:
            print(line)
