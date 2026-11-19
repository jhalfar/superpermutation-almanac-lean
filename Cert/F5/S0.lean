import Cert.F5Def

namespace SuperpermLowerBounds
namespace Cert
namespace F5

noncomputable section

def n2230 : CS := pth 3 0x0505b9
def n13898 : CS := chd 5 n2230 0x0f11110305
def n30095 : CS := chd 9 n2230 0x030505031111110305
def n46815 : CS := chd 10 n2230 0x03050505031111110305

end

end F5
end Cert
end SuperpermLowerBounds
