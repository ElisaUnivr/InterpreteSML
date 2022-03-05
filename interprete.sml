(* Elisa Acciari, Matricola VR478828
Implementazione 3° Esercizio
*)


load "Listsort"; (*carichiamo le librerie di moscow ml*)
load "Int";
load "Bool";
(*carichiamo  la libreria Random per implementare la Par e la Choice con la scelta non deterministica*)
load "Random";

datatype type_loc = intref 


type loc = string
type store = (loc * int) list (* tipo dello store *)

datatype type_L1= 
	int
	|bool
	|unit
	|proc 

(*dichiaro un nuovo tipo per implementare le operazioni piu e maggioreuguale*)
datatype oper = piu | maggioreuguale 

datatype exp =
        Boolean of bool
    |   Integer of int
	|	String of string
	| 	Var of int
    |   Skip 
    |   Op of exp * oper * exp
    |   If of exp * exp * exp
    |   Assign of loc * exp
    |   Seq of exp * exp 
    |   While of exp * exp
    |   Deref of loc
	| 	Let of type_L1 * exp * exp 
	|	Par of exp * exp
	|	Choice of exp * exp 
	| 	Await of exp * exp 


val gen = Random.newgen()
(*Genera un numero casuale tra 0 ed 1*)
fun rand() =
	SOME (Random.range(0, 2) gen)

(*Valuta asserzioni*)
fun valore (Integer n) = true
  | valore (Boolean b) = true
  | valore (Skip) = true
  | valore _ = false

(*Ritorna il valore di una locazione l in uno store*)
fun lookup ( [], l ) = NONE
  | lookup ( (l',n')::pairs, l) = 
    if l=l' then SOME n' 
	else lookup (pairs,l)(*Chiama lookup finchè non si giunge nella locazione l*)

(*Aggiorna il valore di una locazione l in uno store*)
fun update'  front [] (l,n) = NONE
 |  update'  front ((l',n')::pairs) (l,n) = 
    if l=l' then 
        SOME(front @ ((l,n)::pairs) )
    else 
        update' ((l',n')::front) pairs (l,n)

fun update (s, (l,n)) = update' [] s (l,n) 

(*Sostituisce e ad n nel 3° parametro*)
fun sostituisci e n (Integer n') = Integer n'
| sostituisci e n (Boolean b) = Boolean b
| sostituisci e n (Op (e1,opr,e2)) = Op (sostituisci e n e1,opr,sostituisci e n e2)
| sostituisci e n (If (e1,e2,e3)) = If (sostituisci e n e1, sostituisci e n e2, sostituisci e n e3)
| sostituisci e n (Assign (l,e1)) = Assign(l,sostituisci e n e1)
| sostituisci e n (Deref l) = Deref l
| sostituisci e n (Skip) = Skip
| sostituisci e n (Seq (e1,e2)) = Seq (sostituisci e n e1,sostituisci e n e2)
|sostituisci e n (While(b,e1))= While(sostituisci e n b, sostituisci e n e1)
|sostituisci e n (Var x) = 
	if x=n then e else (Var x)
|sostituisci e n (Let(x,e1,e2))= Let(x, sostituisci e n e1, sostituisci e n e2) 
|sostituisci e n (Await(e1,e2))= Await( sostituisci e n e1, sostituisci e n e2) 
|sostituisci e n (Par(e1,e2))= Par( sostituisci e n e1, sostituisci e n e2) 
|sostituisci e n (Choice(e1,e2))= Choice( sostituisci e n e1, sostituisci e n e2) 


	
(*SMALL STEP*)	
	
(*Riduzioni dei vari costrutti*)
fun red (Skip,s) = NONE  
	| red (Boolean b,s) = NONE
	| red (Integer n,s) = NONE
	| red (Op (e1,oper,e2),s) = 
		(case (e1,oper,e2) of
			 (Integer x1, piu, Integer x2) => SOME(Integer (x1+x2), s)   (*op+*)
		   | (Integer x1, maggioreuguale, Integer x2) => SOME(Boolean (x1 >= x2), s)(*op>=*)
		   | (e1,oper,e2) => (                                               
			 if (valore e1) then (                                        
				 case red (e2,s) of 
					 SOME (e2',s') => SOME (Op(e1,oper,e2'),s')     (*op2*)
				   | NONE => NONE )                           
			 else (                                                 
				 case red (e1,s) of 
					 SOME (e1',s') => SOME(Op(e1',oper,e2),s')      (*op1*)
				   | NONE => NONE ) ) )
	| red (If (e1,e2,e3),s) =
		(case e1 of
			 Boolean(true) => SOME(e2,s)                           
		   | Boolean(false) => SOME(e3,s)                          
		   | _ => (case red (e1,s) of
					   SOME(e1',s') => SOME(If(e1',e2,e3),s')      (*if*)
					 | NONE => NONE ))
	| red (Deref l,s) = 
	(case lookup  (s,l) of                
		  SOME n => SOME(Integer n,s)                          
		| NONE => NONE )
	| red (Seq (e1,e2),s) =                                   
		(case e1 of                                                 
			Skip => SOME(e2,s)                                     
			| _ => ( case red (e1,s) of                           
					 SOME (e1',s') => SOME(Seq (e1',e2), s')       
				   | NONE => NONE ) )  
	| red (Let(t,e1,e2),s) =
		(if valore( e1 ) then
			SOME(sostituisci e1 0 e2,s) (* (let2) *)
		else (
			case red (e1,s) of (* (let1) *)
				SOME(e1',s') => SOME(Let(t,e1',e2),s')
				|NONE => NONE
			))
	| red (Assign (l,e),s) =                                  
		(case e of                                                 
		 Integer n => (case update (s,(l,n)) of 
						   SOME s' => SOME(Skip, s')           
							| NONE => NONE)                                   
	   | _ => (case red (e,s) of                           
				   SOME (e',s') => SOME(Assign (l,e'), s')    
				 | NONE => NONE  ) )                          
	| red (While (e1,e2),s) = SOME( If(e1,Seq(e2,While(e1,e2)),Skip),s)                   
	
	
	(*Estensione linguaggio while*)
	
	(*Somma non deterministica*)
	| red (Choice (e1,e2),s) =
		(case rand() of (*genero un numero casuale tra 0 e 1, in base a questo scelgo il ramo da eseguire*)
	(*ChoiceL*)		SOME(0) => (case red(e1,s) of 
						SOME (e1', s') => SOME (e1',s')
						|NONE=> NONE)
	(*ChoiceR*)		|SOME(1)=>( case red (e2,s) of                           
						 SOME (e2',s') => SOME(e2', s')       
						| NONE => NONE ))
						
	(*Composizione Parallela*)
	| red (Par (e1,e2),s) =
		(case rand() of (*genero un numero casuale tra 0 e 1, in base a questo scelgo il ramo da eseguire*)
	(*par-L*)SOME(0) =>  (case red(e1,s) of 
							SOME (e1', s') => SOME(Par(e1',e2),s')
	(*end-L*)				|_=>  SOME (e2,s))
	(*par-R*)|SOME(1)=>( case red (e2,s) of  
						SOME (e2',s') => SOME(Par(e1,e2'), s')       
	(*end-R*)			| _ => SOME(e1,s)))
						
	(*Costrutto Await*)
	| red (Await(b,e),s) =
	(*creo con la let una funzione locale dentro un'altra funzione, per valutare un espressione in un solo passo*)
		let
			fun evaluate (e,s) = (case red(e,s) of 
									NONE => (e,s)
									|SOME(e',s') => evaluate(e',s')  )
		in
		(case evaluate(b,s) of (*valuto in un solo passo la condizione*)
			 (Boolean true,s') =>(case evaluate(e,s') of (*valuto in un solo passo il corpo*)
									(Skip,s'') => SOME(Skip,s'')
									| _ => NONE )
			| (Boolean false,s') => SOME(Await (b, e),s')  (*se la condizione e' falsa, mi rimetto in attesa con l'Await e ricontrollo la condizione*)
			|_=> NONE
			
		)
		end					
		
	
(*Big Step*)
fun evaluate (e,s) = case red (e,s) of 
                         NONE => (e,s)
                       | SOME (e',s') => evaluate (e',s')
					   
(*Tipaggio*)
fun infertype gamma (Integer n) = SOME int
	| infertype gamma (Boolean b) = SOME bool
	| infertype gamma (Op (e1,oper,e2)) 
	= (case (infertype gamma e1, oper, infertype gamma e2) of
		  (SOME int, piu, SOME int) => SOME int
		| (SOME int, maggioreuguale, SOME int) => SOME bool
		| _ => NONE)
	| infertype gamma (If (e1,e2,e3)) 
	= (case (infertype gamma e1, infertype gamma e2, infertype gamma e3) of
		   (SOME bool, SOME t2, SOME t3) => 
		   (if t2=t3 then SOME t2 else NONE)
		 | _ => NONE)
	| infertype gamma (Deref l) 
	= (case lookup (gamma,l) of
		   SOME intref => SOME int
		 | NONE => NONE)
	| infertype gamma (Assign (l,e)) 
	= (case (lookup (gamma,l), infertype gamma e) of
		   (SOME intref,SOME int) => SOME unit
		 | _ => NONE)
	| infertype gamma (Skip) = SOME unit
	| infertype gamma (Seq (e1,e2))  
	= (case (infertype gamma e1, infertype gamma e2) of
		   (SOME unit, SOME t2) => SOME t2
		 | _ => NONE )
	| infertype gamma (While (e1,e2)) 
	= (case (infertype gamma e1, infertype gamma e2) of
		   (SOME bool, SOME unit) => SOME unit 
		 | _ => NONE )
		 
		 
	(*tipaggi impementati*)
	| infertype gamma (Choice (e1,e2)) 
		= (case (infertype gamma e1, infertype gamma e2) of
			   (SOME unit, SOME unit) => SOME unit 
			 | _ => NONE )
	| infertype gamma (Par (e1,e2)) 
		= (case (infertype gamma e1, infertype gamma e2) of
				(SOME unit, SOME unit) => SOME proc 
				|(SOME unit, SOME proc) => SOME proc 
				|(SOME proc, SOME unit) => SOME proc 
				|(SOME proc, SOME proc) => SOME proc 
				| _ => NONE )
	| infertype gamma (Await (e1,e2)) 
		= (case (infertype gamma e1, infertype gamma e2) of
			   (SOME bool, SOME unit) => SOME unit 
				| _ => NONE );

fun printop piu = "+"
  | printop maggioreuguale = ">="
  
fun extract(a:type_L1) = (case a of	
					int=> "int"
					| bool=> "bool"
					| unit=> "unit"
					| proc=> "proc")
	
 
(*Funzione printexp per la stampa formale delle espressioni*) 
fun printexp (Integer n) = Int.toString n
	| printexp (Boolean b) = Bool.toString b
	| printexp (Op (e1,oper,e2)) = "(" ^ (printexp e1) ^ (printop oper)  ^ (printexp e2) ^ ")"
	| printexp (If (e1,e2,e3)) 	= "if " ^ (printexp e1 ) ^ " then " ^ (printexp e2) ^ " else " ^ (printexp e3)
	| printexp (Deref l) = "!" ^ l
	| printexp (Assign (l,e)) =  l ^ ":=" ^ (printexp e )
	| printexp (Skip) = "skip"
	| printexp (Seq (e1,e2)) =  (printexp e1 ) ^ ";" ^ (printexp e2)
	| printexp (While (e1,e2)) =  "while " ^ (printexp e1 )  ^ " do " ^ (printexp e2)
	| printexp (Choice (e1,e2)) =  (printexp e1 ) ^ " +ch "  ^ (printexp e2) 
	| printexp (Par (e1,e2)) =  (printexp e1 ) ^ " || "  ^ (printexp e2) 
	| printexp (Await (e1,e2)) =  "await "^(printexp e1 ) ^ " protect "  ^ (printexp e2) ^ " end" 
	|printexp (Let(x,e1,e2)) = "let val x: " ^ (extract(x)) ^" = " ^(printexp e1 )^ " in " ^ (printexp e2)^ " end "

	

fun printstore' [] = ""
  | printstore' ((l,n)::pairs) = l ^ "=" ^ (Int.toString n) 
                                   ^ " " ^ (printstore' pairs)
fun printstore pairs = 
    let val pairs' = Listsort.sort 
                         (fn ((l,n),(l',n')) => String.compare (l,l'))
                         pairs
    in
        "{" ^ printstore' pairs' ^ "}" end


fun printconf (e,s) = "< " ^ (printexp e) 
                             ^ " , " ^ (printstore s) ^ " >"


fun printred' (e,s) = 
    case red (e,s) of 
        SOME (e',s') => 
        ( TextIO.print ("\n -->  " ^ printconf (e',s') ) ;
          printred' (e',s'))
      | NONE => (TextIO.print "\n -/->  " ; 
                 if valore e then 
                     TextIO.print "(a value)\n" 
                 else 
                     TextIO.print "(stuck - not a value)" )

fun printred (e,s) = (TextIO.print ("      "^(printconf (e,s))) ;
                          printred' (e,s))

(* 

ESEMPI

val s =[] : store;

PAR

val par = Par(Await(Boolean false, Skip),  Skip);

red(par,s);
>val it = SOME(Await(Boolean false, Skip), []) :(exp * (string * int) list) option

printexp(par);
> val it = "await false protect skip end || skip" : string

infertype [] par;
> val it = SOME proc : type_L1 option


SOMMA DETERMINISTICA

val ch = Choice(Skip, Await(Boolean true, Skip));

red(ch,s);
> val it = NONE : (exp * (string * int) list) option

printexp(ch);
> val it = "skip +ch await true protect skip end" : string

infertype [] ch;
> val it = SOME unit : type_L1 option


AWAIT

val aw = Await(Boolean true, Assign("a", Op(Integer 1, piu, Integer 2)));

red(aw,[("a",1)]);
> val it = SOME(Skip, [("a", 3)]) : (exp * (string * int) list) option

infertype [("a",intref)] aw;
> val it = SOME unit : type_L1 option

printexp(aw);
>val it = "await true protect a:=(1+2) end" : string


 *)