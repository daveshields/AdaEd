with Buggy_Package;
procedure Buggy_Package_Demo is
	function Func_INTEGER
		is new Buggy_Package.Func_INT( INTEGER );
	procedure Proc_INTEGER
		is new Buggy_Package.Proc_INT( INTEGER );
begin
	NULL;
end Buggy_Package_Demo;
