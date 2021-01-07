(*Sistemare map e filter perche' ritornano solo evT list e non l'intero Set oof*)

type ide = string;;
type exp = 
    Eint of int 
    | Ebool of bool 
    | Den of ide 
    | Prod of exp * exp 
    | Sum of exp * exp 
    | Diff of exp * exp 
    | Eq of exp * exp 
    | Minus of exp 
    | IsZero of exp 
    | Or of exp * exp 
    | And of exp * exp 
    | Not of exp 
    | Ifthenelse of exp * exp * exp 
    | Let of ide * exp * exp 
    | Fun of ide * exp 
    | FunCall of exp * exp 
    | Letrec of ide * exp * exp;;



(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

type rapTypes = RBool | RInt | RString ;;

(*tipi esprimibili*)
type evT = Int of int 
| Bool of bool 
| String of string
| Unbound 
| FunVal of evFun 
| RecFunVal of ide * evFun 
(*La forma del nostro set e' composta da il tipo del set e poi da una lista di evT*)
| Set of rapTypes * evT list
and evFun = ide * exp * evT env





(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with

	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	"set" -> (match v with
		Set(_) -> true
		| _ -> false)
		|	_ -> failwith("not a valid type");;

(*funzioni primitive*)
(*Funzione per creare un set vuoto a partire da un qualunque valore esprimibile t*)
let empty (t : rapTypes): evT = match t with
	| RBool -> Set(RBool,[])
	| RInt -> Set(RInt,[])
	| RString -> Set(RString,[])
	| _ -> failwith("Non exisisting type")


let singleton (cont : evT) (typename : rapTypes) : evT=
	match typename with
	| RBool -> Set(RBool,cont::[])
	| RInt -> Set(RInt,cont::[])
	| RString -> Set(RString,cont::[])
	| _ -> failwith("Non existing type");;

let rec haselement (elem : evT) (listset: evT) : bool = 
	match (elem,(listset)) with 
	| (Int(_),Set(RInt,[])) -> false
	| (Bool(_),Set(RBool,[]))-> false
	| (String(_),Set(RString,[])) -> false
	| (Int(_),Set(RInt,h::t)) -> if elem = h then true else haselement elem (Set(RInt,t))
	| (Bool(_),Set(RBool,h::t)) -> if elem = h then true else haselement elem (Set(RBool,t))
	| (String(_),Set(RString,h::t)) -> if elem = h then true else haselement elem (Set(RString,t))
	| _ -> failwith("Not a Set");;

	(*Inserimento in testa*)
let insert(listset : evT) (var : evT) : evT =
	if (haselement var listset) = false then 
	match (listset,var) with
	| (Set(f,[]),y) -> (Set(f,y::[]))
	| (Set(RInt,h::t),Int(x)) -> (Set(RInt,Int(x)::h::t))
	| (Set(RBool,h::t),Bool(x)) -> (Set(RBool,Bool(x)::h::t))
	| (Set(RString,h::t),String(x)) -> (Set(RString,String(x)::h::t))
	| _ -> failwith("Not a Set")
	else listset;;

(*Funzione di supporto per la rimozione di un elemento*)
let rec internalRemove (leest : evT list) (value : evT) : evT list = 
	match leest with
	| [] -> []
	| h::t -> if h = value then t else h::internalRemove t value
	| _ -> failwith("Unexpected case");;

let rec remove(listset : evT) (var : evT) : evT =
	if (haselement var listset) = true then 
	match listset with
	| (Set(f,[])) -> Set(f,[])
	| (Set(RInt,leest)) ->  Set(RInt, internalRemove leest var)
	| (Set(RBool,leest)) -> Set(RBool,internalRemove leest var)
	| (Set(RString,leest)) -> Set(RString, internalRemove leest var)
	| _ -> failwith("NN ho cpt")
	else listset;;


	(*Controlla se il nostro Set e' vuoto*)
let isEmpty (leest : evT) =
	let check (oleest : evT list)= match oleest with
	| [] -> true
	| _ -> false in
	match leest with
		| Set(_,e1) -> check e1
		| _ -> failwith("run-time error");;

(*Set s1 Sott'insieme di Set s2*)

let contains (s1 : evT) (s2 : evT) =
	let rec innercontains (e1 : evT list) (e2 : evT list) =
		match(e1,e2) with
		| (h::t,e2) -> if haselement h s2 then innercontains t e2 else false
		| ([],_) -> true in
		match (s1,s2) with
		| (Set(f,e1),Set(g,e2)) -> if f = g then innercontains e1 e2 else failwith("Types don't match");;
	
(*Controllo elemento minimo nell'insieme*)
let min (s1 : evT) : evT = 
	let rec innermin (e1 : evT list) (minn : evT) : evT = 
		match e1 with 
		| [] -> minn
		| h::t -> if h < minn then innermin t h else innermin t minn in
		match s1 with 
		| Set(f,h::t) -> innermin (h::t) h
		| _ -> failwith("???");;
	
(*Controllo elemento massimo nell'insieme*)
let max (s1 : evT) : evT = 
	let rec innermax (e1 : evT list) (maxx : evT) : evT = 
		match e1 with 
		| [] -> maxx
		| h::t -> if h > maxx then innermax t h else innermax t maxx in
		match s1 with 
		| Set(f,h::t) -> innermax (h::t) h
		| _ -> failwith("???");;
	
let for_all (predicate : evT -> bool) (aSet : evT) =
	let returnList (t : evT) = match t with | Set(_,leest) -> leest in
		let never = returnList aSet in
			List.for_all predicate never;;

let exists (predicate : evT -> bool) (aSet : evT) = 
	let returnList (t : evT) = match t with | Set(_,leest) -> leest in
		let gonna = returnList aSet in
			List.exists predicate gonna;;


let filter (predicate : evT -> bool) (aSet : evT) =
		let returnList (t: evT) = match t with | Set(_,leest) -> leest in	
			let give = returnList aSet in
				let you = List.filter predicate give in 
					match aSet with
					| Set(f,_) -> Set(f,you);;

let map (predicate : evT -> evT) (aSet : evT) = 
	let returnList (t: evT) = match t with | Set(_,leest) -> leest in	
		let rec cleanUp (lest : evT list) = 
			match lest with
			| [] -> []
			| h::t::[] -> if h != t then h::t::[] else h::[]
			| h::snd::t -> if h != snd then h::cleanUp (snd::t) else cleanUp (h::t)
			|_ -> failwith("Can't cleanup list") in
		let up = returnList aSet in
			let never = List.map predicate up in 
				match aSet with
				| Set(f,_) -> Set(f,cleanUp never);;
	
		

let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u)| _ -> failwith("???"))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u)| _ -> failwith("???"))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u)
		| _ -> failwith("???"))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u)
		| _ -> failwith("???"))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n)
		| _ -> failwith("???"))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0)
		| _ -> failwith("???"))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e))
		| _ -> failwith("???"))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e)| _ -> failwith("???"))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true)| _ -> failwith("???"))
	else failwith("Type error");;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
        Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
            		_ -> failwith("non functional def"));;
		
(* =============================  TESTS  ================= *)

(* basico: no let *)
let env0 = emptyenv Unbound;;

let e1 = FunCall(Fun("y", Sum(Den "y", Eint 1)), Eint 3);;

eval e1 env0;;

let e2 = FunCall(Let("x", Eint 2, Fun("y", Sum(Den "y", Den "x"))), Eint 3);;

eval e2 env0;;


(*Tests per il nostro Set*)

(*Crea un Set con contentente un singolo elemento  Set(RString,[String "hello"])*)
let testSingleton = singleton  (String("hello")) (RString);;
(*Crea un Set, ma vuoto   Set(RString,[])*)
let testEmpty = empty(RString);;

(*Inserisce in testa al Set*)
let testInsert = insert testSingleton (String("world!"));;
(*Prova ad inserire un elemento gia' esistente nel set,quindi non viene inserito *)
let testInsert = insert testSingleton (String("world!"));;
(*Test rimozione dell'elemento String(hello) *)
let testRemove = remove testInsert (String("hello"));;

let testInsert = insert testInsert (String("Never"));;
let testInsert = insert testInsert (String("Gonna"));;
let testInsert = insert testInsert (String("Give"));;
let testInsert = insert testInsert (String("You"));;
let testInsert = insert testInsert (String("Up"));;


let test = filter (fun elem -> elem < (String("A"))) testInsert;;
if test = Set(RString,[]) then true else false;; 
if (isEmpty test) then true else false;;
let test = map (fun elem -> (String("Mapped"))) testInsert;;
if test = Set(RString,[String("Mapped")]) then true else false;;
let test = for_all (fun elem -> elem < (String("A"))) testInsert;;
if test then true else false;;
let test = exists (fun elem -> elem > (String("z"))) testInsert;;
if test then true else false;;

max testInsert;; (*z *)
min testInsert;; (* Give*)
let test = remove testInsert (String("z"));;


(* test numerici *)
(*Creazione di un set vuoto*)
let y = empty(RInt);;

if (isEmpty y) then true else false ;; (*Ritorna true *)

let y = insert y (Int(1));;
let y = insert y (Int(2));;
let y = insert y (Int(3));;
let y = insert y (Int(4));;
let y = insert y (Int(5));;

max y;;
min y;;

let y = remove (max y);;



