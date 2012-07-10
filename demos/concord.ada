with text_io; use text_io;
with list_package;
procedure concordance is

    package int_io is new integer_io(integer); use int_io;
    package line_list is new list_package(natural); use line_list;

    type vstring is access string;
    type word_node;
    type word_link is access word_node;
    subtype alpha is character range 'A'..'z' ;
	
    type word_node is 
					-- For words in text as stored 
      record				-- in binary search tree.
	word: vstring;
	left: word_link;		-- Link to left child.
	right: word_link;		-- Link to right child.
	times: integer;			-- Count of occurrences.
	lines: list;			-- Header for line number list.
      end record;


    root: word_link := null;		-- Root of binary search tree.

    procedure tree_search(word: in vstring) is separate;
-- Procedure to search for word in tree. If search fails, new node is
-- created for it.


    procedure print_node(node: in word_node) is separate;	    
-- Print out information pertaining to word in text.


    procedure tree_traverse(node: in word_link) is separate;
-- Procedure performs inorder traversal of binary tree.

function get_string return string is
   n : character ;
   buffer : string(1..100) ;
   len: integer := 0 ;
   
begin
   get(n) ;

   while (n not in alpha) loop  get(n) ; end loop ;

   while (n in alpha) loop
       len := len + 1 ;
       buffer(len) := n ;
       if end_of_line then exit; end if ;
       get(n) ;
   end loop ;

   return buffer(1..len) ;
end get_string ;
			    
begin
    -- Read words from text file into binary search tree.
    loop
	declare
	    x: vstring := new string'(get_string);
	begin
	    new_line;
	    put_line("Next word in text: ");
	    put_line(x.all);
	    tree_search(x);	-- Search for word in tree.		
	end;
    end loop;

exception 
    when end_error => 
	new_line(5);
	put_line("Alphabetized list of words in text: ");
	new_line(2);
	tree_traverse(root);	-- Print out contents of tree.

end concordance;


separate(concordance)						    
procedure tree_search(word: in vstring) is

    linenum : natural;
    cur_node: word_link;

    function make_node return word_link is
    -- Enter new node in binary tree.
	x : word_link;
	q : list := empty_list;

    begin
	append(q, natural(line(standard_input)));
	x := new word_node'
			( word =>  word,
			  left =>  null, 
			  right => null, 
			  times => 1, 
			  lines => q);
	return x;

    end make_node;


begin
    -- check if tree empty
    if root = null then
	put_line("make root node");
	root := make_node;
	return;
    end if;

    cur_node := root;				-- Search nonempty tree.
    loop 
	put_line("node examined: ");
	put_line(cur_node.word.all);
	if cur_node.word.all = word.all then    -- Word already seen.
	    put_line("word already seen");
	    cur_node.times :=
		cur_node.times + 1;
	    linenum := natural(line(standard_input));
	    if last(cur_node.lines) /= linenum then
		-- Add line number to list if not already present.
		append(cur_node.lines, linenum);
	    end if;
	    return;
	elsif cur_node.word.all > word.all then
	    if cur_node.left = null then 
		put_line("attach left child");
		cur_node.left := make_node; 	-- Attach left child.
		return;
	    else			        -- Search left subtree.
		put_line("search left subtree");
		cur_node := cur_node.left;
	    end if;
	else
	    if cur_node.right = null then  	-- Attach right child.
		put_line("attach right child");
		cur_node.right := make_node;
		return;
	    else			        -- Search right subtree.
		put_line("search right subtree");
		cur_node := cur_node.right;
	    end if;
	end if;
    end loop;

end tree_search;



separate(concordance)
procedure print_node(node: in word_node) is

    procedure print_list is
    -- Print out contents of (non-empty) line number list,
    -- from front to rear.
	
	cur_lines : list;
	item : natural;

    begin
	cur_lines := node.lines;
	put_line("Appears on line numbers: ");
	loop
	    remove(cur_lines, item);
	    put(item);
	    put(" ");
	    if is_empty(cur_lines) then
	        new_line;
		return;
	    end if;
	end loop;

    end print_list;


begin
    put_line(node.word.all);
    put_line("Number of times word appears: ");
    put(node.times);
    new_line;
    print_list;			-- Print contents of line number list.
    new_line;
    return;

end print_node;


separate(concordance)
procedure tree_traverse(node: in word_link) is
-- Inorder traversal of binary tree.

begin
    if node = null then return; end if;

    tree_traverse(node.left);		-- Traverse left subtree.
    print_node(node.all);
    tree_traverse(node.right);		-- Traverse right subtree.

    return;

end tree_traverse;
