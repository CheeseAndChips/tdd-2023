import struct
import types
import marshal

class CodeObj:
    def __init__(self, argcount, posonlyargcount, kwonlyargcount, \
                       stacksize, flags, code, consts, names, localsplusnames, \
                       localspluskinds, filename, name, qualname, firstlineno, \
                       linetable, exceptiontable):
        self.argcount = argcount
        self.posonlyargcount = posonlyargcount
        self.kwonlyargcount = kwonlyargcount
        self.stacksize = stacksize
        self.flags = flags
        self.code = code
        self.consts = consts
        self.names = names
        self.localsplusnames = localsplusnames
        self.localspluskinds = localspluskinds
        self.filename = filename
        self.name = name
        self.qualname = qualname
        self.firstlineno = firstlineno
        self.linetable = linetable
        self.exceptiontable = exceptiontable

def mark_flag(c: str) -> bytes:
    assert len(c) == 1
    return bytes([ord(c) | 0x80])

def dump_byte(x: int) -> bytes:
    assert x < 256
    return bytes([x])

def dump_long(x: int, ignore_flag=False) -> bytes:
    retval = b''
    if not ignore_flag:
        retval += mark_flag('i')
    retval += struct.pack('I', x)
    return retval

def dump_len(x: int, ignore_flag=False) -> bytes:
    return dump_long(x, ignore_flag=ignore_flag)

def dump_tuple(x: tuple) -> bytes:
    retval = b''
    if len(x) < 256:
        retval += mark_flag(')')
        retval += dump_byte(len(x))
    else:
        retval += mark_flag('(')
        retval += dump_len(len(x))

    for o in x:
        retval += dump_obj(o)
    return retval

def dump_code(x: CodeObj) -> bytes:
    retval = b''
    retval += mark_flag('c')
    retval += dump_long(x.argcount, ignore_flag=True)
    retval += dump_long(x.posonlyargcount, ignore_flag=True)
    retval += dump_long(x.kwonlyargcount, ignore_flag=True)
    retval += dump_long(x.stacksize, ignore_flag=True)
    retval += dump_long(x.flags, ignore_flag=True)
    retval += dump_obj(x.code)
    retval += dump_obj(x.consts)
    retval += dump_obj(x.names)
    retval += dump_obj(x.localsplusnames)
    retval += dump_obj(x.localspluskinds)
    retval += dump_obj(x.filename)
    retval += dump_obj(x.name)
    retval += dump_obj(x.qualname)
    retval += dump_long(x.firstlineno, ignore_flag=True)
    retval += dump_obj(x.linetable)
    retval += dump_obj(x.exceptiontable)
    return retval

def dump_bytes(x: bytes, ignore_flag=False) -> bytes:
    retval = b''
    if not ignore_flag:
        retval += mark_flag('s')
    retval += dump_len(len(x), ignore_flag=True)
    retval += x
    return retval

def dump_str(x: str, ignore_flag=False) -> bytes:
    retval = b''

    enc = x.encode()
    if len(enc) < 256:
        if not ignore_flag:
            retval += mark_flag('Z')
        retval += dump_byte(len(enc))
    else:
        if not ignore_flag:
            retval += mark_flag('a')
        retval += dump_len(len(enc), ignore_flag=True)
    retval += enc
    return retval

def dump_obj(x) -> bytes:
    if type(x) == tuple:
        return dump_tuple(x)
    elif type(x) == int:
        return dump_long(x)
    elif type(x) == CodeObj:
        return dump_code(x)
    elif type(x) == bytes:
        return dump_bytes(x)
    elif type(x) == str:
        return dump_str(x)
    elif x == None:
        return b'N'
    else:
        raise Exception(f'Do not know type: {type(x)}')

def run_test(obj):
    a = dump_obj(obj)
    b = marshal.dumps(obj)

    if a != b:
        print('Mismatch!')
        print(a)
        print(b)
        assert False

test_code = '''
def test_func(x):
    print(5 * x)
'''

def generate_bytecode():
    return bytes([151, 0, 100, 1, 100,
            0, 122, 0, 83, 0])
    return b'\x97\x00' + \
           b'\x64\x01' + \
           b'\x64\x02' + \
           b'\x7a\x00\x00\x00' + \
           b'\x53\x00'

def generate_creator():
    return b'\x97\x00' + \
           b'\x64\x00' + \
           b'\x84\x00' + \
           b'\x5a\x00' + \
           b'\x79\x01'

def run_tests():
    
    lololol = CodeObj(
        0, 0, 0, 2, 3,
        bytes([151, 0, 100, 1, 83, 0]), ('sveikas', 'pasauli'), (), (), b'', # idk del cia
        '<string>', 'func', 'func', 1, b'', b''
    )
    print(dump_obj(lololol.code))
    print(dump_obj(lololol))
    # return

    # run_test(1)
    # run_test((1, 2))
    # run_test(b'\x97\x00d\x00\x84\x00Z\x00y\x01')
    # run_test('str')
    # run_test((None, 'str'))
    print(marshal.loads(dump_obj(tuple(i for i in range(253)))))

    test_compile = compile(test_code, '<string>', 'exec')
    from_mar = marshal.dumps(test_compile)
    print()
    print(from_mar)


# "co_argcount", "co_posonlyargcount", "co_kwonlyargcount", "co_stacksize", "co_flags", "co_code", "co_consts", "co_names", "co_localsplusnames", "co_localspluskinds", "co_filename", "co_name", "co_qualname", "co_firstlineno", "co_linetable", "co_exceptiontable"

#class CodeObj(
#    argcount: Unknown,
#    posonlyargcount: Unknown,
#    kwonlyargcount: Unknown,
#    stacksize: Unknown,
#    flags: Unknown,
#    code: Unknown,
#    consts: Unknown,
#    names: Unknown,
#    localsplusnames: Unknown,
#    localspluskinds: Unknown,
#    filename: Unknown,
#    name: Unknown,
#    qualname: Unknown,
#    firstlineno: Unknown,
#    linetable: Unknown,
#    exceptiontable: Unknown
#)

    test_function = CodeObj(
        0, 0, 0, 2, 3,
        generate_bytecode(), (None, 5, 7), (), (), b'', # idk del cia
        '<string>', 'func', 'func', 1, b'', b''
    )

    from_me = dump_obj(CodeObj(
        0, 0, 0, 2, 3,
        generate_creator(), (test_function, None), ('func',), (), b'', # idk del cia
        '<string>', '<module>', '<module>', 1, b'', b''
    ))
    
    loaded_from_me = marshal.loads(from_me)
    import dis
    dis.dis(loaded_from_me)
    input()

    for a in dir(loaded_from_me):
        if not a.startswith('co_'):
            continue
        b = getattr(loaded_from_me, a)
        print(f'{a}: {type(b)} {b}')

    print()
    print(from_me)
    print()

    module = types.ModuleType('<dynamic>')
    print(eval(loaded_from_me, module.__dict__))
    print(module.func())
    return

    amount_matches = 0
    for a, b in zip(from_mar, from_me):
        if a != b:
            break
        amount_matches += 1

    print(f'Matching: {amount_matches}')
    print(from_me[:amount_matches])
    print(f'Diverge mar {from_mar[amount_matches:]}')
    print(f'Diverge me  {from_me[amount_matches:]}')


run_tests()

