# variables
AT LEAST scoreboard variables must be natively supported
Storage is debatable - I've never really worked with them, and when I do its usually unintended

# file structure
I really liked zoglin's module structure so I think I'll just use that.

# control flow

if-else, while will be implemented "as expected"

I like JMTs async loops, so I think I will add that as well

for loop will be the basic i in range loop.

# execute

There should be a way to do almost everything execute does with the syntax of the language itself,
without having to call execute. Schedule is also included as something we want to eliminate

Examples so far:
if statements
`@condition` for things that can't be expressed as normal expressions
spawn loops/spawn calls
Things to do:
Make it so builtins can take blocks, so we don't have to keep adding 5 morbillion keywords
