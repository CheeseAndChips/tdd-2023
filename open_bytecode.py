import sys
import marshal
data = sys.stdin.read()
lst = bytes(eval(data))
code = marshal.loads(lst)

if '-d' in sys.argv:
    import dis
    print(lst)
    print(code)
    print(code.co_code.hex())
    dis.dis(code.co_code)
    print('\n\n---------------')
    dis.dis(code)
    print('\n\n---------------')

res = eval(code)
print('-----')
print(res)
