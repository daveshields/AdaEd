-- gen_.ada
with TEXT_IO;
use  TEXT_IO;

generic
  MAX_STRING_LENGTH: in POSITIVE;
package DYNAMIC_STRING is
  subtype STRING_LENGTHS is INTEGER range 0 .. MAX_STRING_LENGTH;
  subtype STRING_INDICES is STRING_LENGTHS;
  type DYNAMIC_STRINGS(LENGTH: STRING_LENGTHS := 0) is private;
  function LENGTH (PASCAL_STRING: DYNAMIC_STRINGS) return STRING_INDICES;
private
  type DYNAMIC_STRINGS(LENGTH: STRING_LENGTHS := 0) is record
    STRING_ARRAY: STRING (1 .. LENGTH);
  end record;
end DYNAMIC_STRING;

package body DYNAMIC_STRING is
  function LENGTH (PASCAL_STRING: DYNAMIC_STRINGS) return STRING_INDICES is
  begin
    return PASCAL_STRING.LENGTH;
  end;
end DYNAMIC_STRING;

with DYNAMIC_STRING;
package STRING_80 is new DYNAMIC_STRING(MAX_STRING_LENGTH => 80);

with string_80;
procedure foo is
  s : string_80.dynamic_strings;
begin
  null;
end;

