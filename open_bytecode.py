import sys
import marshal
data = sys.stdin.read()
lst = bytes(eval(data))
print(lst)
code = marshal.loads(lst)
print(eval(code))
