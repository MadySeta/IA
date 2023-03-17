%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de fa�on synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reuss
 déterminer tous les nit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Ps (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Ps
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************

main :- initial_state(S0),
	G0 is 0,
	heuristique1(S0,H0),
	F0 is G0+H0,
	empty(Pf),
	empty(Pu),
	empty(Q),
	insert([[F0,H0,G0],S0],Pf,Pfnew),
	insert([S0, [F0,H0,G0], nil, nil],Pu,Punew),
	aetoile(Pfnew,Punew,Q).

%*******************************************************************************

%cas trivial 1
aetoile([], [], _Qs) :-
	write('PAS DE SOLUTION : L’ETAT FINAL N’EST PAS ATTEIGNABLE ! ').
aetoile(Pf,Pu,Q):-
	suppress_min([V,U],Pf,_),
	(
	final_state(U) ->
		belongs([U,V,Pere,A],Pu),
		insert([U,V,Pere,A],Q,Qf),
		afficher_solution(Qf,[U,V,Pere,A])
	;
		suppress_min([[Ff,Hf,Gf],Uf],Pf,IntermPf),
		belongs([Uf,[Ff,Hf,Gf],Pere,Action],Pu),
		suppress([Uf,[Ff,Hf,Gf],Pere,Action],Pu,IntermPu),
		
		expand([[_,_,Gf],Uf],Suc),
		loop_successors(Suc,IntermPu,IntermPf,Q,NewPu,NewPf),

		insert([Uf,[Ff,Hf,Gf],Pere,Action], Q, NewQ),
		aetoile(NewPf, NewPu, NewQ)
	).

	
expand([[_F,_H,G],U], Successors):-
	findall([V,[Fv,Hv,Gv],U,Av], 
	(rule(Av,Kuv,U,V) , heuristique(V,Hv), Gv is G+Kuv, Fv is Hv+Gv),
	Successors).

test_expand():-
	initial_state(Ini),
	G0 is 0,
	expand([[_,_,G0],Ini], _Suc).


loop_successors([],Pu,Pf,_,Pu,Pf).
loop_successors([First|Rest], Pu, Pf, Q, Punew, Pfnew):-
	treat(First,Pu,Pf,Q,Puaux,Pfaux),
	loop_successors(Rest,Puaux,Pfaux,Q,Punew,Pfnew).

treat([V,[F,H,G],U,A],Pu,Pf,Q,Punew,Pfnew):-
	((belongs([V,[_F,_H,_G],_U,_A],Q))->
		Punew=Pu,
		Pfnew=Pf
		;
		(suppress([V,[Fold,Hold,Gold],_Pold,_Aold],Pu,Puaux)->
			([F,H,G]@<[Fold,Hold,Gold]->
				suppress([[Fold,Hold,Gold],V],Pf,Pfaux),
				insert([[F,H,G],V],Pfaux,Pfnew),
				insert([V,[F,H,G],U,A],Puaux,Punew)
			;
				Punew=Pu,
				Pfnew=Pf
			)
			
	;
			insert([V,[F,H,G],U,A],Pu,Punew),
			insert([[F,H,G],V],Pf,Pfnew)
			
		)
	).

test_treat():-
	initial_state(Ini),
	G0 is 0,
	heuristique2(Ini,H0),
	F0 is G0+H0,
	empty(Pf),
	empty(Pu),
	empty(Q),
	insert([[F0,H0,G0],S0],Pf,Pfaux),
	insert([S0, [F0,H0,G0], nil, nil],Pu,Puaux),
	expand([[F0,H0,G0],Ini], Suc),
	loop_successors(Suc,Puaux,Pfaux,Q,Punew,Pfnew),
	writeln('Punew :'),
	put_flat(Punew),
	writeln(''),
	writeln('Pfnew : '),
	put_flat(Pfnew).



afficher_solution(Q,[U,Val,_Pere,A]):-
	suppress([U,Val,P,A],Q,Qp),
	(belongs([P,Valp,Perep,Ap],Qp) ->
		afficher_solution(Qp,[P,Valp,Perep,Ap]),
		writeln(A),
		write_state(U)
		;
		writeln('Début')
	).


test_execution_time(T):-
	statistics(cputime, Start_Time),
	main,
	statistics(cputime, End_Time),
	T is End_Time-Start_Time.
