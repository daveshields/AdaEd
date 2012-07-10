with Text_IO;
procedure Test_End_Of_File is
        file : Text_IO.FILE_TYPE;
        last : CHARACTER := ' ';
begin
        Text_IO.Open( file, Text_IO.IN_FILE, "abc" );
        loop
                exit when Text_IO.End_Of_File( file );
                begin
                        Text_IO.Get( file, last );
                exception
                        when Text_IO.END_ERROR =>
                                Text_IO.Put_Line( "Get: END_ERROR" );
                                raise;
                end;
--              Text_IO.Put( last );
        end loop;       -- EXIT
        Text_IO.Close( file );
end Test_End_Of_File;

--After compiling, binding, and executing, the program generates
--an END_ERROR exception when it hits the end of file ! but it should not
--since the statement above the Get has just tested for end of file !

