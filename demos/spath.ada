-- A parallel  single-source, all-destinations shortest-path finder. 
-- Each  task is  assigned a node,  and tries  to extend the path by 
-- cloning new tasks that explore all successors of that node.
-- The graph is  represented by adjacency lists. This representation
-- is fixed, and global to all tasks.
-- The minimum distances at each step of the computation are kept in
-- arrays RESULT and COMING_FROM. These objects are  monitored by an
-- array of tasks, one for each node, to  yield greater concurrency.

with TEXT_IO; use TEXT_IO;
procedure shortest_path is
    package i_io is new integer_io(integer);
    use i_io;

    n: integer := 4;				-- cardinality of graph
    subtype graph_size is integer range 1..n;
    subtype graph_node is graph_size ;
    inf: integer := 9999;			-- Infinite distance

    type config is array(graph_size) of integer;
    adjacency: array(graph_size) of config;	-- To describe the graph
    result: config := (graph_size => inf);	-- Shortest distances
    coming_from: config;			-- To reconstruct paths
begin
    declare
        task type monitor_node is
	    entry init(node: graph_node) ;

	    entry go_on(pred: graph_node; 
		        pathlength: integer; 
		        shorter: out boolean);
        end monitor_node;
	
	monitor: array(graph_size) of monitor_node ;

        task type path is
	    entry init(node, pred:  graph_node; 
		       pathlength, size: integer);
        end path;

        type path_name is access path;
        start: path_name;
        subtype s_path is path;


        task body monitor_node is
	    here: graph_node ;		-- node monitored by this task
        begin
	    accept init(node: graph_node) do 
		here := node ; 
	    end init ;

	    loop select
	        accept go_on(pred: graph_node;
			     pathlength: integer;
			     shorter:    out boolean) 
	        do
	            if pathlength < result(here) then
			-- new path is shorter than previous attempts.
		        result(here) := pathlength;
			coming_from(here) := pred;
		        shorter := true;
	            else
		        shorter := false;
	            end if;
	        end go_on;
	        or
		    terminate;
                end select;
            end loop;
        end monitor_node;

        task body path is
	    source, from: graph_node;
	    cost,edge: integer;
	    options: config;
	    x: path_name;
	    response: boolean;
        begin
	    accept init(node, pred: graph_node;
			pathlength,size: integer) 
	    do
	        source := node;
		from   := pred;
	        cost   := pathlength;
 	        edge   := size;
	    end init;

	    cost:=cost+edge;
	    monitor(source).go_on(from, cost, response);
	    if response then	
	        -- found shorter path than previous attempts.
		-- Clone successors to explore edges out of this node.

	        options := adjacency(source) ;
	        for j in graph_size loop
		    if options(j) /= inf then	      -- edge exists;
		        x := new s_path ;	      -- new task for it
		        x.init(j, source, cost, options(j));    
		    end if;
	        end loop;
	    end if;
        end path;

    begin
        adjacency :=((inf, 9, 2, inf), (inf, 1, 1, 2), 
		     (inf, 2, inf, 5), (inf, 1, inf, 2) );

	for j in graph_size loop
	    -- Attach a monitor_node to each graph node.
	    monitor(j).init(j) ;
        end loop ;

        start := new path;
	start.init(1, 1, 0, 0);	     -- start from node 1, distance 0.
    end; 			     -- and wait for tasks to terminate.

    put_line("Final distances from source") ;
    new_line; 

    for j in graph_size'succ(graph_size'first).. graph_size'last 
    loop 
	put(result(j));
	put("   to  ")  ; put(j) ;
	put("  reached via ")  ; put(coming_from(j)) ; 
	new_line;
    end loop;
end shortest_path;

