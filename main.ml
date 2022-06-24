open Graphics;;
open List;;
open Random;;

type coord = { x :int ; y : int } ;;

type salle = { 
	ouest : bool;
	nord  : bool;
	est   : bool;
  sud   : bool;
};;

type chemin = coord list;;

type 'a quadtree = Vide | Feuille of 'a | Noeud of 'a quadtree * 'a quadtree * 'a quadtree * 'a quadtree;;

type labyrinthe = {
  cote : int;(*Une puissance de 2*)
  lab : salle quadtree
};;

let gen_cote = function
	| 0 -> 8
	| n when n = 1 || n = 2 -> 16
	| _ -> failwith "Erreur";;

let rec create_arbre = function
	| 0 -> failwith "Erreur 0 atteint"
	| 1 -> let p = {ouest = bool() ; nord = bool(); est = bool(); sud = bool()} in  Feuille(p)
	| n -> Noeud(create_arbre (n/2),create_arbre (n/2),create_arbre (n/2),create_arbre (n/2));;

let rec find_room (x,y) c = function
	| Noeud(no,ne,so,se) when (c<>2)-> if (x<(c/2))
            													then if (y<(c/2))
            														then find_room (x,y) (c/2) (no) 
            														else find_room (x,y-(c/2)) (c/2) (so) 
            												 else if (x>=(c/2))
            														then if (y<(c/2))
            														then find_room (x-(c/2),y) (c/2) (ne) 
            														else find_room (x-(c/2),y-(c/2)) (c/2) (se) 		
            													else failwith "Erreur dimension"
	|	Noeud(no,ne,so,se) when c = 2 ->	if (x mod 2) = 0 
																				then if (y) mod 2 = 0 
																						 then find_room (x,y) (c/2) (no)	
																						 else find_room (x,y) (c/2) (so)
																			else if (x mod 2 = 1)																			
																				 then if (y mod 2 = 0) 
																							then find_room (x,y) (c/2) (ne)
																							else find_room (x,y) (c/2) (se)
																			else failwith "Erreur dimension"
	| Feuille(p) -> p
	| _ -> failwith "Erreur";;

let construire_case (x,y) laby n =
	let ybis = laby.cote-1-y in
	if n = 1 then set_color black else set_color yellow;
  draw_rect (x * 48) (ybis * 48) 48 48;
	let p = find_room (x,y) laby.cote laby.lab in
	let a=x*48 in
	let b=ybis*48 in
	if (p.ouest = true) then draw_segments [|a+12,b+15,a+3,b+24|] else ();
	if (p.ouest = true) then draw_segments [|a+3,b+24,a+12,b+33|] else ();
	if (p.nord = true) then draw_segments [|a+15,b+36,a+24,b+45|] else ();
	if (p.nord = true) then draw_segments [|a+24,b+45,a+33,b+36|] else ();
	if (p.est = true) then draw_segments [|a+36,b+15,a+45,b+24|] else ();
	if (p.est = true) then draw_segments [|a+45,b+24,a+36,b+33|] else ();
	if (p.sud = true) then draw_segments [|a+15,b+12,a+24,b+3|] else ();
	if (p.sud = true) then draw_segments [|a+24,b+3,a+33,b+12|] else ();;
	
let construire_laby laby=
	for i = 0 to laby.cote-1  do
		for j= 0 to laby.cote-1 do
			construire_case (i,j) laby 1
		done 
	done;;

let rec chemin_possible laby = function 
	| [] -> ()
	| a :: b -> construire_case a laby 2;
							chemin_possible laby b;;

let pop p =
	match p with
	| [] -> ((-2,-2),[])
	| hd :: tl ->  (hd,tl);; 


let rec find_sorties_verticales (x,y) laby sortie = 
	if x=0 then 
		if y<laby.cote then 
			let p = find_room (x,y) laby.cote laby.lab in
			if p.ouest=true then find_sorties_verticales (x,y+1) laby ((x,y)::sortie) else find_sorties_verticales (x,y+1) laby sortie
		else find_sorties_verticales (laby.cote-1,0) laby sortie
	else if y<laby.cote then 
				let p = find_room (x,y) laby.cote laby.lab in
				if p.est=true then find_sorties_verticales (x,y+1) laby ((x,y)::sortie) else find_sorties_verticales (x,y+1) laby sortie
			else sortie;;
			
let rec find_sorties_horizontales (x,y) laby sortie = 
	if y=0 then 
		if x>0&&x<laby.cote-1 then 
			let p = find_room (x,y) laby.cote laby.lab in
			if p.nord=true then find_sorties_horizontales (x+1,y) laby ((x,y)::sortie) else find_sorties_horizontales (x+1,y) laby sortie
		else find_sorties_horizontales (1,laby.cote-1) laby sortie
	else if x>0&&x<laby.cote-1 then 
			let p = find_room (x,y) laby.cote laby.lab in
				if p.sud=true then find_sorties_horizontales (x+1,y) laby ((x,y)::sortie) else find_sorties_horizontales (x+1,y) laby sortie
			else sortie;;						
						
let sorties_laby	laby =
	(find_sorties_verticales (0,0) laby [])@(find_sorties_horizontales (1,0) laby []);;
																
let bloque (x,y) laby deja_vu=
	let p = find_room (x,y) laby.cote laby.lab in
	((p.ouest=false)||(mem (x-1,y) deja_vu))&&((p.nord=false)||(mem (x,y-1) deja_vu))&&((p.est=false)||(mem (x+1,y) deja_vu))&&((p.sud=false)||(mem (x,y+1) deja_vu));;

let move laby (x,y) deja_vu =
	let p = find_room (x,y) laby.cote laby.lab in
	if (p.ouest=true)&&(x<>0)&&(not(mem (x-1,y) deja_vu)) then (x-1,y) else
	if (p.nord=true)&&(y<>0)&&(not(mem (x,y-1) deja_vu)) then (x,y-1) else
	if (p.est=true)&&(x<>laby.cote-1)&&(not(mem (x+1,y) deja_vu)) then (x+1,y) else
	if (p.sud=true)&&(y<>laby.cote-1)&&(not(mem (x,y+1) deja_vu))then (x,y+1) else (48,48);;
																																																																																																									
let go_out cord sortie laby =
	let rec go_to (x,y) sortie laby pile deja_vu=
			let pos = (x,y) in
		 	if not(mem pos sortie) then 
				if (not(bloque pos laby deja_vu)&&pos<>(48,48)) then let next = move laby pos deja_vu in
					go_to next sortie laby ((x,y)::pile) ((x,y)::deja_vu)
				else let pp=pop pile in if (fst(pp)<>(-2,-2)) then go_to (fst(pp)) sortie laby (snd(pp)) ((x,y)::deja_vu) else []
			else rev(pos::pile)
	in go_to (cord.x,cord.y) sortie laby [] [];;

let draw_pos (x,y) color laby=
  set_color color;
  fill_circle (x*48+24) ((laby.cote-1-y)*48+24) 10 ;
  set_color red;;

let graph_size n =
	match n with
	| 8 -> open_graph" 384x384"
	| 16 -> open_graph" 768x768"
	| _ -> failwith "Erreur";;

let draw_plateau laby pos sortie=
	clear_graph();
	construire_laby laby;
	let sortie_ok = (go_out pos sortie laby) in
	if  sortie_ok = []
	then draw_pos (pos.x,pos.y) black laby 
	else  if sortie_ok = [(pos.x,pos.y)] 
				then draw_pos (pos.x,pos.y) green laby
				else draw_pos (pos.x,pos.y) red laby;;

let trois_premiers liste =
	let rec cut_list liste n new_list=
  	match n with 
  	| 0 -> new_list
  	| n -> match liste with
  				| [] -> new_list
  				| curr::next ->cut_list next (n-1) (curr::new_list)
	in cut_list liste 3 [];;

let jouer ()  = 
	let c=gen_cote (int(3)) in
	let labyrinthe={cote=c; lab=create_arbre c} in
	graph_size c;
	let a=int(labyrinthe.cote) in
	let b=int(labyrinthe.cote) in
	let cord = {x = a; y = b} in
	let sorties = sorties_laby labyrinthe in
	let rec tour_de_jeu laby pos sortie cpt =
		draw_plateau laby pos sortie;
		if cpt = 1 then chemin_possible laby (trois_premiers (go_out pos sortie laby))
		else if cpt = 2 then chemin_possible laby (go_out pos sortie laby) else ();
		let p = find_room (pos.x,pos.y) laby.cote laby.lab in
		let pressed=read_key() in
		match pressed with
		| 'z' when pos.y <> 0 && p.nord=true -> tour_de_jeu laby ({x=pos.x;y=pos.y-1}) sortie 0
		| 'q' when pos.x <> 0 && p.ouest=true -> tour_de_jeu laby ({x=pos.x-1;y=pos.y}) sortie 0
		| 's' when pos.y <> laby.cote-1 && p.sud=true -> tour_de_jeu laby ({x=pos.x;y=pos.y+1}) sortie 0
		| 'd' when pos.x <> laby.cote-1 && p.est=true -> tour_de_jeu laby ({x=pos.x+1;y=pos.y}) sortie 0
		| 'p' -> close_graph()
		| 'i' -> tour_de_jeu laby pos sortie 1
		| 'a' -> tour_de_jeu laby pos sortie 2
		| 'e' when (go_out pos sortie laby) = [(pos.x,pos.y)] -> close_graph()
		| _ -> tour_de_jeu laby pos sortie 0
	in tour_de_jeu labyrinthe cord sorties 0;;

jouer();;