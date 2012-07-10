      WITH Calendar;
      PROCEDURE FunnyBug IS
      
      -- minimal version of a student error on which adasem choked.
      
      BEGIN
        NULL;
      EXCEPTION
      
      -- note a careless writing of Time_Error as Time.Error
     
       WHEN Calendar.Time.Error =>
         NULL;
     END FunnyBug;
