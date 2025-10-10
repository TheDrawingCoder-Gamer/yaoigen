# TODO

- [X] Add zig-like while increments
- [ ] Actually handle Arrays & Compounds
- [X] Add for loop
- [ ] Eventually get around to nested returns again
- [X] Add basic builtins
- [ ] continue/break
- [ ] labelled continue/break ?

Continue:

```
while $a < 10 |$a += 1| {
    if $c {
        `say hi`
        continue
    }
}
```

compiles into two functions:

while/fn_0
```
# condition
execute unless score $a example matches ..9 run return 0
execute if score $c example matches (fullintrange) unless score $c matches 0 run function ziglin:generated/if/fn_0
# TODO: how to check for nested continue?
# continue expression (increment)
scoreboard players add $a example 1
# recurse
function ziglin:generated/while/fn_0
```

if/fn_0
```
say hi
scoreboard 
```