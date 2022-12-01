module Parentheses where 

data Form : Set where
    [] * : Form
    -- [_] : Form → Form

-- record Marked Form : Set where
--     constructor [_]
--     field
--         a : Form

[_] : Form → Form
[ [] ] = []
[ * ]  = []