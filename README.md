# HappyTree

Happy Tree is a end-to-end decision tree library in Haskell.

That mean, it's main selling point is, while most decision tree library support splitting on Discrete Category/Continuous Variable (Read: essentially Int and Double), Happy Tree let you split on any type, as long as you specify how to split on it.

Want to decide on List or AST? No Problem!

Want to use your custom quantile search like thingy to speed up splitting on continuous variable? Piece of Cake!

Want to use different split strategy at the same time, splitting on the finest choice? You Name It: It form a monoid.

## Known Problem

Might never return if you insert infinite list or other infinite data.

Can only split on finitely many type now. Cannot split on

data Perfect a = Here a | More (Perfect (a, a)).
