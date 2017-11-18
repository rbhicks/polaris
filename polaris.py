
def assert_node(identity, sources, destinations):

    node_opening     = "(node"
    identity_part    = "(identity " + identity + ")"
    source_part      = "(source-nodes (create$ " + sources + "))"
    destination_part = "(destination-nodes (create$ " + destinations + "))"
    node_closing     = ")"


    assert_string = node_opening + identity_part + source_part + destination_part + node_closing

    clips.Assert(assert_string)
    
def assert_loop_instruction(loop_identity, index, mnemonic, operand0, operand1):

    loop_instruction_opening = "(loop-instruction"
    loop_identity_part       = "(loop-identity " + loop_identity + ")"
    index_part               = "(index " + str(index) + ")"
    mnemonic_part            = "(mnemonic \"" + mnemonic + "\")"
    operand0_part            = "(operand0 \"" + operand0 + "\")"
    operand1_part            = "(operand1 \"" + operand1 + "\")"
    loop_instruction_closing = ")"

    assert_string = loop_instruction_opening + loop_identity_part + index_part + mnemonic_part + operand0_part + operand1_part + loop_instruction_closing

    clips.Assert(assert_string)

def process_nodes():

    ea                  = ScreenEA()
    processed_addresses = set()


    while ea != BADADDR:

        sources      = ""
        destinations = ""


        for source in CodeRefsTo(ea, 1):
            sources = sources + " " + str(source)
        for destination in CodeRefsFrom(ea, 1):
            destinations = destinations + " " + str(destination)

        if hex(ea) not in processed_addresses:
            assert_node(str(ea), sources, destinations)
            processed_addresses.add(hex(ea))

        # Collecting function chunks
        function_instructions = list()

        # Get the tail iterator
        func_iter = idaapi.func_tail_iterator_t(idaapi.get_func(ea))

        # While the iterator's status is valid
        status = func_iter.main()

        while status:
            # Get the chunk
            chunk = func_iter.chunk()

            # Go through all instructions in the basic block
            # and add them to our list
            #
            for head in Heads(chunk.startEA, chunk.endEA):
                if isCode(idaapi.getFlags(head)):
                    function_instructions.append(head)

            # Get the last status
            status = func_iter.next()
    
        nodes = dict()

        for address in function_instructions:
            refs_to        = CodeRefsTo(address, 1)
            refs_from      = CodeRefsFrom(address, 1)
            refs           = (refs_to, refs_from)
            nodes[address] = refs

        for key in nodes.keys():
            sources      = ""
            destinations = ""

            for source in nodes[key][0]:
                sources = sources + " " + str(source)
            for destination in nodes[key][1]:
                destinations = destinations + " " + str(destination)

            if hex(key) not in processed_addresses:
                assert_node(str(key), sources, destinations)
                processed_addresses.add(hex(key))
        
        ea = NextFunction(ea)

import clips

def process_loop_instructions(identity, loop_nodes):
    loop_nodes.pop()
    i = 0
    for node in loop_nodes:
        address     = hex(node)
        instruction = GetMnem(node)
        operand0    = GetOpnd(node, 0)
        operand1    = GetOpnd(node, 1)

        assert_loop_instruction(identity, i, instruction, operand0, operand1)
        i = i + 1

def print_hex_list(x):
    print "========================================================="
    for y in x:
        print hex(y)
    print "========================================================="

def print_line(x):
    print x

def print_hex(x):
    print hex(x)

def print_node(identity, sources, destinations):
    print "identity: %s" % (hex(identity))
    for source in sources:
        print "source: %s" % (hex(source))
    for destination in destinations:
        print "destination: %s" % (hex(destination))
    print


def print_enclosing_function(node):
    ea = node[0]
    function_ea = idaapi.get_func(ea).startEA


    if function_ea != BADADDR:
        print "enclosing function adddress: %s" % (hex(function_ea))
    else:
        print "bad enclosing function address"

def write_loop_instructions(identity, first_node, last_node, loop_nodes):
    loop_nodes.pop()
    line = "id: %s\nfirst node: %s\n" % (identity, hex(first_node))
    g_log_file.write(line)
    for node in loop_nodes:
        address     = hex(node)
        instruction = GetMnem(node)
        operand0    = GetOpnd(node, 0)
        operand1    = GetOpnd(node, 1)
        line = "%s:  %s %s %s\n" % (address, instruction, operand0, operand1)
        g_log_file.write(line)
    line = "last node: %s\n" % (hex(last_node))
    g_log_file.write(line)
    g_log_file.write("\n\n")


g_log_file = open("\\\\.psf\\xp shared\\projects\\vb2008\\loop-instructions.txt", 'w')



clips.Clear()
clips.RegisterPythonFunction(print_node)
clips.RegisterPythonFunction(print_line)
clips.RegisterPythonFunction(print_hex)
clips.RegisterPythonFunction(print_hex_list)
clips.RegisterPythonFunction(print_enclosing_function)
clips.RegisterPythonFunction(write_loop_instructions)
clips.RegisterPythonFunction(process_loop_instructions)
clips.Load("\\\\.psf\\xp shared\\projects\\vb2008\\polaris.clp")
clips.Reset()
process_nodes()
clips.Run()

g_log_file.close()

print "done"
