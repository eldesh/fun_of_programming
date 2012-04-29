
signature SUSP =
sig
  type 'a susp
  val delay : (unit -> 'a) -> 'a susp
  val force : 'a susp -> 'a
end

(* if SMLofNJ *)
structure Susp = SMLofNJ.Susp

(*
(* if not SMLofNJ *)
(* emulating the Susp module of SML/NJ *)
structure Susp : SUSP =
struct
  datatype 'a susp = S of unit -> 'a
  fun delay f = S f
  fun force (S thunk) = thunk ()
end
*)

signature LAZYLIST =
sig
  include SUSP
  datatype 'a lazylist = lnil | ::: of 'a * 'a lazylist susp
  val tail : 'a lazylist -> 'a lazylist
  val head : 'a lazylist -> 'a
  val null : 'a lazylist -> bool
  val fromN : int -> int lazylist
  val range : int -> int option -> int lazylist
  val all : ('a -> bool) -> 'a lazylist -> bool
  val any : ('a -> bool) -> 'a lazylist -> bool
  val take : int -> 'a lazylist -> 'a lazylist
  val drop : int -> 'a lazylist -> 'a lazylist
  val -!- : 'a lazylist -> 'a list
  val -?- : 'a list -> 'a lazylist
  val filter : ('a -> bool) -> 'a lazylist -> 'a lazylist
  val append : 'a lazylist -> 'a lazylist -> 'a lazylist
  val ++ : 'a lazylist * 'a lazylist -> 'a lazylist
  val map : ('a -> 'b) -> 'a lazylist -> 'b lazylist
  val foldl : ('b -> 'a -> 'b) -> 'b -> 'a lazylist -> 'b
  val foldr : ('a -> 'b -> 'b) -> 'b -> 'a lazylist -> 'b
  val reverse : 'a lazylist -> 'a lazylist
  val zipped : 'a lazylist -> 'b lazylist -> ('a * 'b) lazylist
  val zipWith : ('a * 'b -> 'c) -> 'a lazylist -> 'b lazylist -> 'c lazylist
  val flatten : 'a lazylist lazylist -> 'a lazylist
  val cycle : 'a -> 'a lazylist
  val dropWhile : ('a -> bool) -> 'a lazylist -> 'a lazylist
  val takeWhile : ('a -> bool) -> 'a lazylist -> 'a lazylist
  val fromReader : ('b, 'a) StringCvt.reader -> 'a -> 'b lazylist
  val repeat : 'a -> 'a lazylist
end

structure LazyList :> LAZYLIST = struct
local
  (*** ---> SML/NJ workaround ***)
  infixr 5 :::
  infix  5 ++
  infixr 1 $
  (* infix    >>= *)
  (*** SML/NJ workaround <--- ***)
in
  fun f $ a = f a
  open Susp
  datatype 'a lazylist = lnil | ::: of 'a * 'a lazylist susp

  fun tail (_ ::: xs) = force xs
    | tail  lnil = raise Empty

  fun null lnil = true
    | null _    = false

  fun head ((x:::xs) : 'a lazylist) : 'a = x
    | head (lnil     : 'a lazylist) = raise Empty

  fun fromN n = n ::: delay (fn ()=>fromN (n+1));

  fun all f lnil = true
    | all f (x:::xs) = if f x then all f (force xs)
                       else false

  fun any f lnil = true
    | any f (x:::xs) = if f x then true
                       else any f (force xs)

  fun take 0 xs  = lnil
    | take _ lnil= lnil
    | take n xs  = (head xs) ::: delay (fn ()=>take (n-1) $ tail xs)

  fun drop 0 xs = xs
    | drop n xs = drop (n-1) $ tail xs

  fun -!- (xs : 'a lazylist) : 'a list = (* change lazy list to strict list *)
    let
      fun strict lnil     = []
        | strict (y:::ys) = y::(strict $ force ys)
    in strict xs
    end

  fun -?- (xs : 'a list) : 'a lazylist = (* change strict list to lazy list *)
    let
      fun lazy []      = lnil
        | lazy (y::ys) = y:::(delay (fn ()=>lazy ys))
    in lazy xs
    end

  fun range from NONE      = from ::: delay (fn ()=> range (from+1) NONE)
    | range from (SOME to) = if to<from
                             then lnil
                             else from ::: delay (fn ()=> range (from+1) (SOME to))
  fun filter f lnil     = lnil
    | filter f (x:::xs) = if (f x)
                          then x::: delay (fn ()=>filter f $ force xs)
                          else filter f $ force xs
  fun append lnil     ys = ys
    | append (x:::xs) ys = x::: delay (fn ()=>append (force xs) ys)
  fun op++ (xs,ys) = append xs ys;

  fun map f lnil     = lnil
    | map f (x:::xs) = f x ::: delay (fn ()=>map f $ force xs)

  fun foldl (e:'b -> 'a -> 'b) (x:'b) (xs: 'a lazylist) : 'b =
    let
      fun foldl_ acc lnil     = acc
        | foldl_ acc (y:::ys) = foldl_ (e acc y) $ force ys
    in foldl_ x xs
    end

  fun foldr (e:'a -> 'b -> 'b) (x:'b) (xs:'a lazylist) : 'b =
    let
      fun foldr_ acc lnil     = acc
        | foldr_ acc (y:::ys) = e y (foldr_ acc (force ys))
    in foldr_ x xs
    end
    
  fun reverse xs = foldl (fn xs=>fn x=>x:::(delay (fn ()=>xs))) lnil xs

  fun zipped _  lnil = lnil
    | zipped lnil  _ = lnil
    | zipped xs  ys = (head xs, head ys)::: delay (fn ()=>zipped (tail xs) (tail ys))

  fun zipWith _    _ lnil = lnil
    | zipWith _ lnil    _ = lnil
    | zipWith f (x:::xs) (y:::ys) = f (x,y):::delay (fn()=> zipWith f (force xs) (force ys))

  fun flatten (xxs:'a lazylist lazylist) : 'a lazylist =
    let
      fun flat lnil      = lnil
        | flat (y:::yys) =
        case y of
             (y:::ys) => -?-[y] ++ (force ys) ++ (flat $ force yys)
           | lnil     => flat $ force yys
    in flat xxs
    end

  fun cycle (x:'a) : 'a lazylist = x ::: delay (fn ()=>cycle x)

  fun dropWhile (p:('a -> bool)) (xs:'a lazylist) : 'a lazylist =
    let
      fun f lnil     = lnil
        | f (ls as (x:::xs)) = if p x
          then f $ force xs
          else ls
    in f xs
    end

  fun takeWhile (p:('a -> bool)) (xs:'a lazylist) : 'a lazylist =
    let
      fun tw lnil     acc = reverse acc
        | tw (y:::ys) acc = if p y
                            then tw (force ys) (y ::: delay (fn ()=>acc))
                            else reverse acc
    in tw xs lnil
    end

  fun fromReader rd v : 'b lazylist =
    case rd v of
         SOME (x, vs) => x ::: delay (fn ()=>fromReader rd vs)
       | NONE         => lnil

  fun repeat x = x:::delay(fn()=> repeat x)

end (* local *)
end (* struct lazylist *)



