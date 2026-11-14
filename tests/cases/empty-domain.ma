-- Positive counterpart to legacy badterm.ma: explicitly eliminate an empty input.
data Empty : Set {}

fun eliminate : Empty -> Empty {}
