# Yaoigen

YAOI FOR EVERYONE!

Yaoigen is a mcfunction transpiler, that transpiles from yaoi to mcfunction.

## Feature overview

### Variables

There are 2 variable types you can store to: storage, and scoreboard.

Storage paths have no prefix:
```
x = 1
```

The path that a storage stores to is dependent on the current namespace and function. You can also specify exact paths if you need to have
global variables:
```
namespace foo {
    module bar {
        fn run() {
            :baz/x = 1 // expands to "storage foo:baz x"
            bar:x = 1 // expands to "storage bar: x"
            ~/x = 1 // expands to "storage foo:bar x"
            x = 1 // expands to "storage foo:bar/run x"
        }
    }
}
```

Scoreboard variables are prefixed with `$`, and are translated similarly to storage variables, but can also have their exact "player name" specified:
```
namespace foo {
    module bar {
        fn run() {
            $:baz/x = 1 // expands to "scoreboard $x foo.baz"
            $bar:x = 1 // expands to "scoreboard $x bar"
            $~/x = 1 // expands to "scoreboard $x foo.bar"
            $x = 1 // expands to "scoreboard $x foo.bar.run"
            $:biz/[@p] // expands to "scoreboard @p foo.biz"
        }
    }
}
```

You can also directly specify the storage name and path, using builtins and indexing/member access:

```
@storage(:baz).x
// entities and block entities too, although these are context sensitive
@entity("@n[type=armor_stand]").Health
@block_entity(~0, ~0, ~0).Items
```

### Control Flow

You can do if statements:

```
if $x {
    say hi
}

if $x {
    say hi
} else if $y {
    say bye
} else {
    say pie
}
```

You can use conditional operators:

| Symbol | Function    |
|---     | ---         |
| and    | boolean and |
| or     | boolean or  |
| ==     | equal to    |
| !=     | unequal to  |
| >      | greater than |
| <      | less than |
| >= | greater than or equal to |
| <= | less than or equal to |
| ! | unary not |

You can also check the truthyness of variables, which will
check to make sure that scoreboard variables aren't unset.

If there's a check that's not implemented, you can use the `@check` builtin:

```
if @check("entity @n[type=armor_stand]") {
    say just standing around
}
```

This translates directly to the condition in `execute if`.

You can do `for` and `while` loops:

```
for $x in 1 to 10 {
    say hi
}

for $x in 0 until 10 {
    say hi
}

for $x in 0 until $:max {
    say hi
}

$x = 0
while $x < $:max |$x += 1| {
    say hi
}

$good = true
while $good {
    // do something
    $good = false
}
```

You can label loops, and break out of them:

```
$x = 0
label: while true {
    $x += 1
    if $x == 5 {
        continue :label
    }
    if $x == 10 {
        break :label
    }
    say hi
}
```

You can "spawn" loops, and have them execute over time:

```
@:spawn(10t) for $x in 0 until 10 {
    say hi
}
say this will be printed after the first hi, but before the rest!
```

You can break spawned loops, ending them early. You can also continue spawned loops, waiting the delay time for the next iteration.

You can also spawn functions:

```
@:spawn(10t) some_func()
// equivilant to adding "append" at the end of the schedule call
@:spawn_append(10t) some_func()
```

### Functions, namespaces and modules

Your root file will contain namespace(s):

```
namespace foo {
    // ...
}
```

You can declare modules directly inside your namespace, or you can delegate them to another file:

```
namespace foo {
    module bar {
        // ...
    }
    // delegates to ./baz.yaoi
    module baz
}
```

Delegated modules in files other than the root file will be in a subdirectory:
```
// in ./baz.yaoi
// delegates to ./baz/buzz.yaoi
module buzz 
```

Instead of making it a submodule, you can also directly include all members in the current file:
```
namespace foo {
    // will take all members of ./baz.yaoi and put them in namespace foo
    use module baz
}
```

You can define functions inside the namespace or module:
```
namespace foo {
    fn some_func() {
        say hi
    }
}
```

Functions can have arguments that get filled in at the call site:
```
namespace foo {
    fn some_func(a, $b, %c) {

    }
}
```
Arguments with no prefix are stored in storage, prefixed with `$` are stored as scoreboard variables, and `%` are passed as macro args.

Arguments can have defaults:
```
fn some_func($a = 1)
```

### Commands

Most vanilla commands that can be executed in normal datapacks without configuring the server can run _unquoted_:

```
say hi
gamemode creative
```

You can insert arguments into a command:
```
// insert resource location, parsed like storage but the name isn't seperate
dialog show @s &{:select_action}
// inserted as function {function identifier}
schedule &{func()} 10t
// inserted as you'd expect, $foo namespace.module.path
scoreboard players set &{$foo} 1
// statements inside block compiled in seperate function, then that function call is inserted
execute as @a run &!{
    say hi
    gamemode creative
}

// like above, but the function is inlined, if possible
execute as @a run &!!{
    $a += 1
}
// builtin, see builtins
scoreboard players reset &{@scoreboard_string(a)}

// insert a macro arg
say %m
// guard macro arg from other characters
say &{%m}b
```

### Builtins

There are builtins and decorators:

Builtins are special functions that generate code specially, and are implemented in the compiler.
Decorators can decorate certain declarations and statements: `@:spawn` is a decorator.

Expression statements with multiple decorators get folded right, like so:
```
@:at("@a") @:as("@s") func()
// compiles as...
@at("@a", @as("@s", func()))
```

This is made specifically for execute builtins, but it also lets you express `spawn` and `spawn_append` differently:
```
@spawn(10t, func())
@spawn_append(10t, func())
```

Some builtins work at the toplevel, some work in inserts.
Here's a list of builtins:

#### @scoreboard
Position: top level, statements

Args: path, criteria (default dummy)

Defines a scoreboard that gets defined before your load function.

#### @reset
Position: statement

Args: Either a string and a path, or a scoreboard variable

Shortcut for `scoreboard players reset &{$var}`

#### @enable
Position: statement

Args: Either a string and a path, or a scoreboard variable

Shortcut for `scoreboard players enable &{$var}`

#### @check
Position: expression

Args: string

Given the bit that comes after `execute if`, translates it into a condition that works in an `if` statement.

#### @is_block
Position: expression

Args: x: block_pos, y: block_pos, z: block_pos

Compiles into a `if block x y z` condition. `block_pos` supports
caret and tilde notation.

#### @scoreboard_string
Position: inserts

Args: path

Inserts _only_ the objective name that would be calculated for this path

#### @spawn, @spawn_append
Position: statements

Args: time: delay, call: function_call_expr

Schedules the `call` for `time`.

`@spawn_append` appends the function to the schedule instead of replacing.

`delay` is a number with an optional suffix s, t, or d.
If the suffix is t or it is missing, the unit is ticks.
If it's s, it's seconds, and if its d, its in-game days.

#### @store_from
Position: statements

Args: start with either `@bossbar(boss_identifier, max | value)`,  a scoreboard variable, or a NBT assignment target with a numeric kind and a scale. Ends with with either a scoreboard or storage path.

Stores the scoreboard or storage into the destination.


#### @storage
Position: expression

Args: storage identifier, optionally nbt path

Returns a storage location from the identifier and path.

#### @entity
Position: expression

Args: selector, optionally nbt path

Returns a data location corresponding to the entity and nbt path

#### @block_entity

Position: expression

Args: x: block_pos, y: block_pos, z: block_pos, optionally an nbt path

Returns a data location corresponding to the block entity at x y z.

#### @execute
Position: statement

Given at least 1 _execute component_ builtins, and a final block or function call, build an execute command

##### execute components
These components may either be used as an argument to `execute`, or standalone, with a nested last argument that is either another execute component or the final block or function call.

This nesting allows these to be chained as statement decorators

###### @as, @at
Args: selector

Map directly to `as $selector` and `at $selector`

###### @align
Args: axes: string

Maps to `align $axes`

###### @anchored
Args: anchor: ("eyes" or "feet")

Maps to `anchored $anchor`

###### @facing
Args: either 3 positions, or a selector with an anchor

Maps to either `facing $x $y $z` or `facing entity $selector $anchor`

###### @in
Args: string with dimension identifier

Maps to `in $dimension`

###### @on
Args: relation: string

Maps to `on $relation`

###### @positioned
Args: either selector or 3 positions

Maps to either `positioned as $selector` or `positioned $x $y $z`

###### @rotated
Args: either selector or 2 rotations (yaw and pitch)

Maps to either `rotated as $selector` or `rotated $yaw $pitch`

Yaw and pitch are numbers that can be in the tilde format.

###### @store_success, @store_result
Args: same as the beginning arguments of `@store_from`

maps to `store success` or `store result`












