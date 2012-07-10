However, I have found the following bug, having to do with end_of_file
detection:

-----8<-----CUT-HERE-----8<-----
BUG #1: The following is returned:

Rule  5: COMP -> 
** parse returned OK
main task terminated due to unhandled exception END_ERROR
propagated from GET_TOKEN at line 104 (End of file on TEXT_IO input)

GET_TOKEN: the lines
[lines deleted from GET_TOKEN]
     if end_of_file then
         state := eof;
         exit;
     end if;
     get(ch);    -- line 104
[further lines deleted]

Sample data:                        
 this is where er  74 68 69 73 20 69 73 20-77 68 65 72 65 20 65 72   
 ror > 8pm and th  72 6F 72 20 3E 20 38 70-6D 20 61 6E 64 20 74 68   
 e rest..          65 20 72 65 73 74 0D 0A                           

However, when the trailing CRLF is removed, the above works with no 
problems.

