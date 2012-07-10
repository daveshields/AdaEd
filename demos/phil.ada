----------------------------------------------------------------------
--
--              The Dining Philosophers' Problem
--
--                      written by
--
--                   Edmond Schonberg
--                        and
--                    Gerry Fisher
--
--                      Ada Project
--                   Courant Institute
--                  New York University
--                   251 Mercer Street
--                New York, New York  10012
--
-----------------------------------------------------------------------

with TEXT_IO; use TEXT_IO; 
procedure DINING_PHILOSOPHERS is
    
    type PHILOSOPHER is (Descartes, Hegel, Turing, Plato, Sartre);

    meals: constant array(PHILOSOPHER) of INTEGER := (3,2,2,2,3);

    Message1: constant array(PHILOSOPHER) of STRING(1 .. 30)  :=
        ("I eat: therefore I am         ",
         "Hegel synthesizes             ",
         "Turing shifts                 ",
         "Plato eats the ideal spaghetti",
         "Sartre gorges                 "
	 );

    Message2: constant array(PHILOSOPHER) of STRING(1 .. 30)  :=
        ("Descartes cogitates           ",
         "Hegel's pure spirit at work   ",
         "Turing machinates             ",
         "Plato watches the shadows     ",
         "Sartre eats nothing           "
	 );

    Message3: constant array(PHILOSOPHER) of STRING(1 .. 30)  :=
        ("Descartes concludes           ",
         "The owl of Minerva is stuffed ",
         "Turing halts                  ",
         "Plato retreats                ",
         "Sartre is nauseated           "
	 );

    task type DINING is
	entry WHO_AM_I(p: PHILOSOPHER);
    end DINING;

    task TABLE_MANAGER is
        entry EAT(PHILOSOPHER);
        entry REST(p: PHILOSOPHER);
	entry FAST_RELIEF(p: PHILOSOPHER);
    end TABLE_MANAGER;

    task body DINING is separate;
 
    task body TABLE_MANAGER is separate;
 
begin

    declare
	PHILS: array(PHILOSOPHER) of DINING;
    begin
	for philo in PHILOSOPHER
	loop
	    PHILS(philo).WHO_AM_I(philo);
	end loop;
    end;

    put_line("Closing time ...");

end DINING_PHILOSOPHERS;

-----------------------------------------------------------------------

separate(DINING_PHILOSOPHERS)
task body DINING is

    philo: PHILOSOPHER;

begin

    accept WHO_AM_I(p: PHILOSOPHER) do
	philo := p;
    end WHO_AM_I;

    for n in 1 .. meals(philo) 
    loop
        TABLE_MANAGER.EAT(philo);
        delay 1.0;
        TABLE_MANAGER.REST(philo);
	delay 0.5;
    end loop;

    TABLE_MANAGER.FAST_RELIEF(philo);

end DINING;


------------------------------------------------------------------------

separate(DINING_PHILOSOPHERS) 
task body TABLE_MANAGER is
 
    type AVAIL is 
	record 
	    LEFT, RIGHT: BOOLEAN; 
	end record;

    FORKS: array(PHILOSOPHER) of AVAIL := 
		(PHILOSOPHER'FIRST..PHILOSOPHER'LAST => (TRUE, TRUE));
    type ACTION is (seize,release);
    numphil: constant INTEGER := 5;
    TWO: constant AVAIL := (TRUE,TRUE);
 
    procedure fork_action(p: PHILOSOPHER; a: ACTION) is separate;
 
begin

    loop
        select
            when FORKS(Descartes) = TWO => 
		accept EAT(Descartes);
                fork_action(Descartes, seize);
		put_line(Message1(Descartes));

	or  when FORKS(Hegel) = TWO => 
		accept EAT(Hegel);
                fork_action(Hegel, seize);
		put_line(Message1(Hegel));

        or  when FORKS(Turing) = TWO => 
		accept EAT(Turing);
                fork_action(Turing, seize);
		put_line(Message1(Turing));

        or  when FORKS(Plato) = TWO => 
		accept EAT(Plato);
                fork_action(Plato, seize);
		put_line(Message1(Plato));
 
        or  when FORKS(Sartre) = TWO => 
		accept EAT(Sartre);
                fork_action(Sartre, seize);
		put_line(Message1(Sartre));

        or      
		accept REST(p: PHILOSOPHER) do
                    fork_action(p, release);
	            put_line(Message2(p));
                end REST;

	or      
		accept FAST_RELIEF(p: PHILOSOPHER) do
		    put_line(Message3(p));
	        end FAST_RELIEF;
        or
            terminate;

        end select ;

    end loop ;

end TABLE_MANAGER ;
 

----------------------------------------------------------------------

separate(DINING_PHILOSOPHERS.TABLE_MANAGER)
procedure fork_action(p: PHILOSOPHER; a: ACTION) is
    pp: PHILOSOPHER;
    v: array(ACTION) of BOOLEAN := (FALSE, TRUE);
begin
    pp := PHILOSOPHER'VAL((PHILOSOPHER'POS(p) + 1) mod numphil);
    FORKS(pp).LEFT := v(a);
    pp := PHILOSOPHER'VAL((PHILOSOPHER'POS(p) + 4) mod numphil);
    FORKS(pp).RIGHT := v(a);
end fork_action;
