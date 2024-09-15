type Node:
  E # Era
  C {a: Node, b: Node} # Con
  D {a: Node, b: Node} # Dup
  V {f: Var -> None} # Var



# A Wire is two variables, each variable accepts a node
# When each variable is linked to a node, they will interact
#
# In order to allow observing the net, as can be seen in the function `Show`,
# a variable can also carry a Fold, which is a function that accepts a node
# If one side of a variable is a node, and the other a fold,
# the node will be applied to the fold.
# However there's also the case in which both sides are a fold,
# for this reason, each fold also carries some data, when two fold meet,
# each fold will get the data of the other.
#
# For example, in the case of Show, the data is the index of the node in the tree.
# Each instance of the function Show will have both its own index,
# and the index of the Show in the other side of the wire.
# In the case of show, the smaller of the two indexes will be chosen,
# giving us a common unique variable name.
# The same idea can also be used to implement an Equals function for two reduced INets.

type Var:
  Node {node: Node}
  Fold {data: Any, f: FoldArg -> None}

type FoldArg:
  Node {node: Node}
  Data {data: Any}

unchecked Wire: (Node, Node)
Wire =
  let w0 = λ$x *
  let w1 = λ$y *
  let * = (VarInteract $x $y)
  ((Node/V w0), (Node/V w1))

VarInteract: Var -> Var -> None

(VarInteract (Var/Node a) (Var/Node b)) = (Interact a b)

(VarInteract (Var/Fold data0 f0) (Var/Fold data1 f1)) =
  let * = (f0 (FoldArg/Data data1))
  let * = (f1 (FoldArg/Data data0))
  *

(VarInteract (Var/Fold data f) (Var/Node node)) = (f (FoldArg/Node node))

(VarInteract (Var/Node node) (Var/Fold data f)) = (f (FoldArg/Node node))

## Interaction

Interact: Node -> Node -> None

# Link

(Interact (Node/V f) (Node/V g)) =
  let (w0, w1) = Wire
  let * = (f (Var/Node w0))
  let * = (g (Var/Node w1))
  *

(Interact (Node/V f) node) = 
  let * = (f (Var/Node node))
  *

(Interact node (Node/V f)) = (Interact (Node/V f) node)

# Erasure

(Interact Node/E Node/E) = *

(Interact Node/E (Node/C a b)) =
  let * = (Interact Node/E a)
  let * = (Interact Node/E b)
  *

(Interact Node/E (Node/D a b)) =
  let * = (Interact Node/E a)
  let * = (Interact Node/E b)
  *

(Interact node Node/E) = (Interact Node/E node)

# Annihilation

(Interact (Node/C a0 b0) (Node/C a1 b1)) =
  let * = (Interact a0 a1)
  let * = (Interact b0 b1)
  *

(Interact (Node/D a0 b0) (Node/D a1 b1)) =
  let * = (Interact a0 a1)
  let * = (Interact b0 b1)
  *

# Commuation

(Interact (Node/C c0 c1) (Node/D d0 d1)) = 
  # Input:
  # (c0 c1) ~ [d0 d1] 
  # Output:
  # c0 ~ [w10a w00a]
  # c1 ~ [w11a w01a]
  # d0 ~ (w10b w11b)
  # d1 ~ (w00b w01b)
  #
  let (w00a, w00b) = Wire
  let (w01a, w01b) = Wire
  let (w10a, w10b) = Wire
  let (w11a, w11b) = Wire
  let * = (Interact c0 (Node/D w10a w00a))
  let * = (Interact c1 (Node/D w11a w01a))
  let * = (Interact d0 (Node/C w10b w11b))
  let * = (Interact d1 (Node/C w00b w01b))
  *

(Interact (Node/D d0 d1) (Node/C c0 c1)) = (Interact (Node/C c0 c1) (Node/D d0 d1))

## Fold

unchecked Node/fold: (Var -> None) -> Any -> Any
(Node/fold var_func data0) = 
  let * = (var_func (Var/Fold data0 λ$arg(*)))
  $arg

## Show

# Paths are used for naming varia
type Bits = (I ~v) | (O ~v) | E
def Bits/to_u24(value):
  fold value:
    case Bits/O:
      return value.v * 2
    case Bits/I:
      return value.v * 2 + 1
    case Bits/E:
      return 1

(String/concat (String/Cons head tail) other) = (String/Cons head (String/concat tail other))
(String/concat String/Nil other) = other

(List/join List/Nil)         = ""
(List/join (List/Cons x xs)) = (String/concat x (List/join xs))


def Min(a: u24, b: u24) -> u24:
  if a <= b:
    return a
  else:
    return b


Show: Node -> Bits -> String

(Show Node/E path) = "*"
(Show (Node/C a b) path) = 
  (List/join [
    "("
    (Show a (Bits/O path))
    " "
    (Show b (Bits/I path))
    ")"
  ])

(Show (Node/D a b) path) = 
  (List/join [
    "["
    (Show a (Bits/O path))
    " "
    (Show b (Bits/I path))
    "]"
  ])

(Show (Node/V f) path) =
  let idx = (Bits/to_u24 path)
  let arg = (Node/fold f idx)
  match arg {
    FoldArg/Node: (Show arg.node path)
    FoldArg/Data: (u24/to_string (Min idx arg.data))
  }

Print: Node -> String
(Print node) = (Show node Bits/E)


main: String
main =
  # The following duplicates "λe e"
  let (a0, a1) = Wire
  let (b0, b1) = Wire
  let (c0, c1) = Wire

  let * = (Interact (Node/C a0 a1) (Node/D b0 c0))
  (List/join [
    (Print b1)
    "\n"
    (Print c1)
  ])
