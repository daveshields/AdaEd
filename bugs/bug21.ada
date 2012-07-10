package p1 is
   type t1 is private ;
private
    type t1 is record
        null;
    end record ;
end ;

with p1; use p1 ;
package p2 is
   subtype same is t1 ;
   thing: same ;
end ;
