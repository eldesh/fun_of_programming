
(**** *****************************************************************************
 *
 * the fun of programming (関数プログラミングの楽しみ)
 *     Jeremy Gibbons and Oege de Moor編 / 山下伸夫訳
 *
 * 
 * example answers with StandardML'97 (SML/NJ)
 * I welcome any advice to my code :)
 **************************************************************************** ****)


structure Fop =
struct
local
  open LazyList
  structure S = String
  infix :::
  infixr 1 $
  fun f $ a = f a
  infix />
  fun f /> y = fn x => f (x,y)
in
  fun wrap x = -?-[x]
  fun const x _ = x

  val % = delay
  val ` = force

  fun ? f x y = f (x,y)

  local
    fun insert x lnil     = wrap x
      | insert x (y:::ys) = if x<y
                            then x::: %(fn()=> y:::ys)
                            else y::: %(fn()=> insert x $ `ys)
  in
    fun isort xs = foldr insert lnil xs
  end
  fun paraL _ e lnil = e
    | paraL f e (x:::xs) = f x (`xs, paraL f e $ `xs)

  (* problem 3.5 *)
  fun insert2 y xs =
  let
    val I = Int.toString
    fun printL e xs ys = print(concat["f ",I e," [", S.concatWith "," (-!- $ map I xs), "] "
                                               ,"[", S.concatWith "," (-!- $ map I ys), "]\n"])
    fun f e (xs, y:::ys) = if e<y (* before printL e xs (y:::ys) *)
                           then e::: %(fn()=> y:::ys)
                           else y::: %(fn()=> e::: %(fn()=> xs))
      | f e (_, _) = wrap e
  in
    paraL f (wrap y) xs
  end

  fun unfoldL p f g b = if p b then lnil
                        else f b::: %(fn()=> unfoldL p f g (g b))

  fun unfoldL' f u = case f u of
                          NONE => lnil
                        | SOME(x,e) => x::: %(fn()=> unfoldL' f e)
  (* problem 3.6 *)
  infix >>=
  fun     NONE >>= _ = NONE
    | (SOME x) >>= f = f x
  fun unfoldL2 p f g b = unfoldL' (fn x=> if p x then NONE
                                          else SOME(f x, g x)) b

  fun unfoldL'2 f u =
    let
      fun p  x = not $ isSome (f x)
      fun f' x = valOf (f x >>= (fn (y,_)=> SOME y))
      fun g  x = valOf (f x >>= (fn (_,y)=> SOME y))
    in
      unfoldL p f' g u
    end

  (*
      -!- $ Fop.unfoldL'2 (fn x=> if x < 10 then SOME(x,x+1) else NONE) 0;
        val it = [0,1,2,3,4,5,6,7,8,9] : int list
      -!- $ Fop.unfoldL'  (fn x=> if x < 10 then SOME(x,x+1) else NONE) 0;
        val it = [0,1,2,3,4,5,6,7,8,9] : int list

      -!- $ Fop.unfoldL2 (fn x=>10<=x) real (fn x=>x*2) 1;
        val it = [1.0,2.0,4.0,8.0] : real list
      -!- $ Fop.unfoldL (fn x=>10<=x) real (fn x=>x*2) 1;
        val it = [1.0,2.0,4.0,8.0] : real list
  *)

  (* problem 3.7 *)
  (* *************************************************************************
   * 
   * h = unfoldL p f g
   *     <=>
   * h b = if p b then Nil else Cons (f b) (h (g b))
   *
   * unfoldL p f g o h = unfoldL p' f' g'
   *     <=>
   * (p o h = p') ^ (f o h = f') ^ (g o h == h o g')
   *
   * unfoldL p  f  g  (i b) = if p (h b) then Nil else Cons (f (h b)) (_ (g (h b)))
   * unfoldL p' f' g' b     = if p'   b  then Nil else Cons (f'    b) (_ (g'   b))
   *
   * -> (p o h = p') ^  (f o h = f') ^ (g o h = g')
   *
   *************************************************************************** *)

  (* preblem 3.8 *)
  fun foldL' f lnil     = f NONE
    | foldL' f (x:::xs) = f (SOME (x, foldL' f $ `xs))
  (*
    - Fop.foldL' (fn(SOME(x,y))=> y-x | NONE=>45) $ -?- [1,2,3,4,5,6,7,8,9];
    val it = 0 : int
  *)

  fun foldL f e xs =
    let fun f' (SOME(x,y)) = f x y | f' NONE = e
    in foldL' f' xs
    end

  (*
    - Fop.foldL (fn x=>fn y=>y-x) 45 $ -?- [1,2,3,4,5,6,7,8,9];
    val it = 0 : int
    - Fop.foldL (fn x=>fn y=>x::y) [] $ -?- [1,2,3,4,5,6,7,8,9];
    val it = [1,2,3,4,5,6,7,8,9] : int list
  *)

  (* problem 3.9 *)
  fun foldLargs (f:'a -> 'b -> 'b) (e:'b) : ('a * 'b) option -> 'b =
    fn (SOME(x,xs))=> f x xs | NONE => e

  (*
    - Fop.foldL' (Fop.foldLargs (fn x=>fn y=>x::y) []) $ L.range 0 (SOME 10);
    val it = [0,1,2,3,4,5,6,7,8,9,10] : int list
  *)

  fun unfoldLargs (p:'b -> bool) (f:'b -> 'a) (g:'b -> 'b) : 'b -> ('a * 'b) option =
    fn x=> if p x then NONE else SOME (f x, g x)

  (*
    - -!- $ Fop.unfoldL' (Fop.unfoldLargs (op> /> 10) Int.toString (op+ /> 2)) 0;
    val it = ["0","2","4","6","8","10"] : string list
    *)

  fun minimumL (x:::xs) = foldL (?Int.min) x $ `xs

  fun deleteL y lnil = lnil
    | deleteL y (x:::xs) = if y=x
                           then `xs
                           else x::: %(fn()=> deleteL y $ `xs)

  fun delmin lnil = NONE
    | delmin xs =
      let val y = minimumL xs
      in SOME (y, deleteL y xs)
      end

  fun ssort xs = unfoldL' delmin xs

  (*
    - -!- $ Fop.ssort $ -?- [8,2,42,10,20,7];
    val it = [2,7,8,10,20,42] : int list
    *)

  (* problem 3.10 *)
  fun deleteL' y xs =
    let fun f e (xs', ys) = if e=y
                            then xs'
                            else e::: %(fn()=> ys)
    in paraL f lnil xs end

  (*
    - -!- $ Fop.deleteL' 5 $ -?- [1,3,5,7];
    val it = [1,3,7] : int list
    *)

  (* problem 3.11 *)
  fun delmin' xs =
    let
      fun f e (xs', NONE) = SOME(e,lnil)
        | f e (xs', SOME(y,ys)) = if e<y
                                  then SOME(e,xs')
                                  else SOME(y,e::: %(fn()=> ys))
    in paraL f NONE xs
    end
  (*
    - Option.map (fn(x,y)=>(x, -!- y)) $ Fop.delmin' $ -?- [8,19,20,2,9,3,6];
    val it = SOME (2,[8,19,20,9,3,6]) : (int * int list) option
    *)

  val I = Int.toString
  fun tup2s (x,y) = print(concat["(",I x,",",I y,")\n"])

  fun bubble xs =
    let
      fun step e NONE = SOME(e,lnil)
        | step e (SOME(y,ys)) = if e<y (* before tup2s (e,y) *)
                                then SOME(e, y::: %(fn()=> ys))
                                else SOME(y, e::: %(fn()=> ys))
    in foldr step NONE xs
    end

  fun bsort xs = unfoldL' bubble xs

  (* problem 3.12 *)
  fun bubble' xs =
    let
      val I = Int.toString
      fun tup2s (x,y) = print(concat["(",I x,",",I y,")\n"])
      fun step e lnil = wrap e
        | step e (x:::xs) = if e<x (* before tup2s (e,x) *)
                            then e::: %(fn()=> x:::xs)
                            else x::: %(fn()=> e:::xs)
    in foldr step lnil xs
    end

  local
    fun I x = x
  in
    fun bsort' xs = unfoldL null (head o bubble') (tail o bubble') xs
  end

  (* problem 3.13 *)
  fun insert' e xs =
    let
      (* take
      *    whether end(NONE) or
      *      (insert element * list will be inserted)
      *)
      fun f NONE = NONE
        | f (SOME(e,  lnil)) = SOME(e,NONE)
        | f (SOME(e,x:::xs)) = if e<x
                               then SOME(e,SOME(x,`xs)) (* copy elements step by step :( *)
                               else SOME(x,SOME(e,`xs))
    in unfoldL' f (SOME(e,xs))
    end

  structure Either =
  struct
    datatype ('a,'b) either = Left of 'a | Right of 'b
    fun isLeft  (Left _)  = true | isLeft _  = false
    fun isRight (Right _) = true | isRight _ = false
  end
  structure E = Either

  fun apoL' f u =
    case f u
      of NONE => lnil
       | SOME(x, E.Left   v) => x::: %(fn()=> apoL' f v)
       | SOME(x, E.Right xs) => x::: %(fn()=> xs) (* use rest of list *)

  (* problem 3.14 *)
  fun insert'' e xs =
    let
      fun f NONE = NONE
        | f (SOME(e,   lnil)) = SOME(e, E.Right lnil)
        | f (SOME(e, x:::xs)) = if e<x (* before tup2s (e,x) *)
                                then SOME(e, E.Right (x:::xs))
                                else SOME(x, E.Left $ SOME(e,`xs))
    in apoL' f $ SOME(e, xs)
    end

  fun hyloL f e p g h b = (* foldL f e o unfoldL p g h b*)
    if p b then e
    else f (g b) $ hyloL f e p g h (h b)

  fun foldleft f e [] = e
    | foldleft f e (x::xs) = foldleft f (f x e) xs
  
  (* problem 3.15 *)
  fun dec2bin (str:string) : bool lazylist =
    let
      val ss = explode str
      fun c2i c = ord c - ord #"0"
      fun f n = if n < 0 then NONE
                else if n=0 then SOME(false, ~1)
                else if n=1 then SOME( true, ~1)
                else SOME(n mod 2=1, n div 2)
    in
      unfoldL' f $ foldleft (fn x=>fn xs=> xs*10 + c2i x) 0 ss
    end

end (* local *)
end


