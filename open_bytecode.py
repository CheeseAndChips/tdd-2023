import sys
import marshal
data = sys.stdin.read()
lst = bytes(eval(data))
code = marshal.loads(lst)

if '-d' in sys.argv:
    import dis
    print(lst)
    print(code)
    dis.dis(code)
    print(list(code.co_code))
    print(code.co_code)
    print('\n\n---------------')

print(eval(code))
