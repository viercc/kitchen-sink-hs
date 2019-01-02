newtype TaggedState a b c x = TaggedState x

data Done

a :: TaggedState () b c x -> TaggedState Done b c x
a = _

b :: TaggedState a () c x -> TaggedState a Done c x
b = _

c :: TaggedState Done b () x -> TaggedState Done b Done x
c = _

d :: TaggedState a Done Done x -> TaggedState a Done Done x
d = _

e :: TaggedState a b c x -> TaggedState a b c x
e = _

process :: TaggedState () () () x -> TaggedState Done Done Done x
process = e . d . c . b . a

anotherProcess :: TaggedState () () () x -> TaggedState Done Done Done x
anotherProcess = d . c . a . b . e
