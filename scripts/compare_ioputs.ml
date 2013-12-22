open Printf


(*Compare 2 files*)
let parse_inp fin: string = 

  let re = (Str.regexp_string "echo")  in
  let found = ref false in
  let inp = ref "" in
  while not !found do
    inp := input_line fin;
    if !inp <> "" then 
      try ignore(Str.search_forward re !inp 0);
      with Not_found -> found := true;
  done;

  let inp = !inp in 
  try
    ignore(Str.search_forward (Str.regexp_string "./tcas.exe") inp 0);
    let pos = Str.match_end () in
    let inp = Str.string_after inp pos in
    
    ignore(Str.search_forward (Str.regexp_string "> ") inp 0);
    let pos = Str.match_beginning () in
      let inp = Str.string_before inp pos in
      inp
  with Not_found -> inp



let compare_outputs (finput: string) (output1: string) (output2: string) = 
  let io_l = ref [] in 

  (try
     let fin = open_in finput in
     let fop1 = open_in output1 in 
     let fop2 = open_in output2 in 
     
     while true do 
       let line0 = parse_inp fin in 
       let line1 = input_line fop1 in 
       let line2 = input_line fop2 in 
       io_l := (line0,line1,line2) :: !io_l ;
     done;
   with _ ->()
  );
  let io_l = List.rev !io_l in

  let same_l, diff_l  = List.partition (fun (_,o1,o2) -> o1 = o2) io_l in
  List.iter (fun (inp,o1,o2) -> printf "(%s) %s %s, " inp o1 o2) same_l ; printf "\n";
  List.iter (fun (inp,o1,o2) -> printf "(%s) %s %s, " inp o1 o2) diff_l ; printf "\n";

  same_l,diff_l

let create_tests fun_name same_l diff_l =

  let mk_test inp outp =     
    let inps = Str.split (Str.regexp "[ \t]+") inp in
    fun_name ^ "(" ^ String.concat "," inps ^ ")  = " ^ outp 
  in

  
  let same_l = List.map (fun (inp,outp,_) -> mk_test inp outp) same_l in
  let diff_l = List.map (fun (inp,outp,_) -> mk_test inp outp) diff_l in

  List.iter (printf "%s\n") diff_l;  printf("\n");
  List.iter (printf "%s\n") same_l;

  ()


let main(): unit = 
  let inps = ref "" in
  let outps1 = ref "" in
  let outps2 = ref "" in

  let argDescr = [] in
  let handleArg s = 
    if !inps = "" then inps := s
    else if !outps1 = "" then outps1 := s
    else if !outps2 = "" then outps2 := s
    else raise (Arg.Bad "too many input files")
  in

  Arg.parse (Arg.align argDescr) handleArg 
    "prog <inputs> <outputs1> <outputs2>";
    
  printf "%s\n" !inps;
  printf "%s\n" !outps1;
  printf "%s\n" !outps2;

  
  let same_l, diff_l  = compare_outputs !inps !outps1 !outps2 in
  create_tests "foo" same_l diff_l;
  ()

let() = main()
