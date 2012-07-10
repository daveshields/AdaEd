PROCEDURE test1 IS
BEGIN
-- missing declaration of n causes this program to crash
  FOR i IN 1..n LOOP 
     NULL; 
  END LOOP;
END test1;
