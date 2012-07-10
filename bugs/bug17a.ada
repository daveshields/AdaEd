-- If you comment out the Nested_Package.Comment_Out_This_Line_And_All_Ok;
-- lines in Buggy_Package, all is well, or if you only comment out one of
-- these lines and don't instantiate the other generic in Buggy_Package_Demo,
-- then all is well.

package Nested_Package is
	procedure Comment_Out_This_Line_And_All_Ok;
end Nested_Package;

package body Nested_Package is
	procedure Comment_Out_This_Line_And_All_Ok is
	begin
		NULL;
	end;
end Nested_Package;

package Buggy_Package is
	generic
		type INT is range <>;
	function Func_INT return INT;
	generic
		type INT is range <>;
	procedure Proc_INT;
end Buggy_Package;

with Nested_Package;
package body Buggy_Package is
	function Func_INT return INT is
	begin
		Nested_Package.Comment_Out_This_Line_And_All_Ok;
		return INT'FIRST;
	end Func_INT;

	procedure Proc_INT is
	begin
		Nested_Package.Comment_Out_This_Line_And_All_Ok;
		null;
	end Proc_INT;
end Buggy_Package;
