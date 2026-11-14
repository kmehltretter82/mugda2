-- An empty argument telescope has one input tuple, even when the result is Empty.
data Empty : Set {}
fun hole : Empty {}
let witness : Empty = hole
