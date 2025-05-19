import Loda.Field

def a : F 5 := 2
def b : F 5 := 3

#eval (a * b)                 -- Expected: 1
#eval ((2 : F 5) + (3 : F 5)) -- Expected 0
#eval (a^2)
#eval (a^3)
#eval (a^4)
#eval (a * b.inv)
