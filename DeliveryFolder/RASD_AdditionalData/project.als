--signature to obtain a true and false value
abstract sig Bool{}
sig True extends Bool{}
sig False extends Bool{}

--image of a violation signature
sig Image {
    accepted : one Bool
}

--license plate of a vehicle committing a violation signature
sig LicensePlate{
    modified : one Bool
}

--authentication types for SafeStreets users
abstract sig AuthenticationType {}
sig SPIDAuthentication extends AuthenticationType {}
sig ProprietaryAuthentication extends AuthenticationType {}

--user details signatures
sig Username{}
sig Password{}

--authentication of a specific user signature
sig Authentication {
    authenticationType : one AuthenticationType,
    username : one Username,
    password : one Password
}

--other user details
sig Name{}
sig Surname{}
sig AuthenticatorID{}
sig FiscalCode{}
sig Address{}
sig PhoneNumber{}
sig Email{}

--location signatures
sig Position{}
sig City{
    position : one Position
}

--abstract user signature containing various details
abstract sig User {
    name : one Name,
    surname : one Surname,
    autheticatorID : one AuthenticatorID,
    authentication : one Authentication,
    reportsMade : set Violation,
    city : one City
}{#authentication.authenticationType=1 or #authentication.authenticationType=2}

--normal user signature containing also more personal details
sig NormalUser extends User {
    reliabilityScore : one Int,
    birthDate : one Date,
    fiscalCode : one FiscalCode,
    birthLocation : one City,
    phoneNumber : one PhoneNumber,
    address : one Address,
    email : one Email,
    view : one ViolationVisualizerLimited
}{reliabilityScore>=0}

--authority signature which is more restrictive
sig Authority extends User {
    authorization : one DigitalCertificateX509,
    notification : set Violation,
    suggestions : set SuggestionsType,
    email : one CertifiedEmail,
    view : ViolationVisualizerPro
}

--date signature for determining time
sig Date{}

--signatures for creating a digital certificateX509
sig ID{}
sig DigitalCertificateX509{
    creationDate : one Date,
    dateOfExpiry : one Date,
    id : one ID
} {creationDate!=dateOfExpiry}

--certified email for authorities
sig CertifiedEmail{}

--violation details signatures and violation signature declaration

sig VehicleType{}
sig ViolationType{}
sig Note{}

sig Violation{
    violationID : one Int,
    violationType : some ViolationType,
    position : one Position,
    timeStamp : one Date,
    vehicleType: one VehicleType,
    image : one Image,
    licensePlate : one LicensePlate,
    note : one Note,
    email : one Email,
    autheticatorID : one AuthenticatorID,
    verified : one Bool
}{#violationType =< 3 and violationID >= 0}

--map displaying a certain area siganture
sig Map{}

--visualizers signature witth different level of visibility 
--containing various violations
abstract sig ViolationVisualizer{
    map : one Map,
    violation : some Violation
}
sig ViolationVisualizerLimited extends ViolationVisualizer{}
sig ViolationVisualizerPro extends ViolationVisualizer{}

--a certain muncipality data signature
sig MunicipalityData {}

--represents Municiplality_i
sig Municipality {
    city : one City,
    incidents : one MunicipalityData
}

--inferring system of SafeStreets siganture
sig SuggestionsType {}

sig SuggestionInferralEngine {
    suggestions : some SuggestionsType,
    municipalities : set Municipality,
    violations : some Violation
}

--no duplicate username is possible so that a certain username is associated with a specific user
fact noDuplicateUsernameNormalUser{
    all u1, u2: NormalUser | (u1.authentication.username = u2.authentication.username) implies u1 = u2
}

--no duplicate user personal details is possible among different users
fact noDuplicateNormalUser {
    all u1, u2 : NormalUser | (u1.autheticatorID = u2.autheticatorID or u1.fiscalCode = u2.fiscalCode  or u1.email = u2.email
             or u1.authentication = u2.authentication or u1.phoneNumber = u2.phoneNumber) implies u1 = u2
}

--each authority has his own personal username which is not replicable
fact noDuplicateUsernameAuthority{
    all u1, u2: Authority | (u1.authentication.username = u2.authentication.username) implies u1 = u2
}

--no duplicate authority detailed data is possible among different authorities
fact noDuplicateAuthority {
    all u1, u2 : Authority | u1 = u2
        iff (u1.autheticatorID = u2.autheticatorID  or u1.email = u2.email or u1.authentication = u2.authentication)
}

--needed to guarantee there not exist any kind of equivalent authorization among different user of every kind
fact noDuplicateAuthorization{
    all a1, a2 : Authority | a1.authorization = a2.authorization implies a1 = a2
}

--for obvious, natural reasons, a city has its own position which is not shared along any other different cities
fact cityPosition{
    all c1, c2 : City | c1.position = c2.position implies c1 = c2
    all u : User  | some c : City | c = u.city
}

--digital certificates X509 cannot have any kind of duplicates to be valid and to respect security measures and constraints
fact noDuplicateDigitalCertificateX509{
    all a1, a2: Authority | a1.authorization.id = a2.authorization.id implies a1.authorization = a2.authorization
    all a : Authority | some c : DigitalCertificateX509 | c = a.authorization
    all c1, c2 : DigitalCertificateX509 | c1 = c2 iff c1.id = c2.id
}

--needed to guarantee a quite important requirement which is that no user can report multiple times the same violation
fact noDuplicateViolationsFromUser {
    all v1, v2 : Violation | 
    (v1.timeStamp = v2.timeStamp or v1.email = v2.email or v1.autheticatorID = v2.autheticatorID)
    implies v1.violationID = v2.violationID
    all u : User | some v : Violation | v in u.reportsMade
    all v1, v2 : Violation | v1 = v2 iff v1.violationID = v2.violationID
    all u1, u2 : User | no v : Violation | u1 != u2 and v in u1.reportsMade and v in u2.reportsMade
}

fact noDuplicateViolationsPerUser{
    all u : NormalUser | some v : Violation | v in u.reportsMade implies (v.email = u.email
        and (some a : Authority | v in a.notification))
}

--this fact guarantees that there are no violations where one of them have a violation type list containing violation type duplicates
fact noDuplicateViolationTypes {
    all vt, vt', vt'' : ViolationType, v: Violation | 
        ((#v.violationType=3 and vt in v.violationType and vt' in v.violationType and vt'' in v.violationType) 
            implies (vt != vt' and vt' != vt'' and vt != vt'')) or
        ((#v.violationType=2 and vt in v.violationType and vt' in v.violationType) implies (vt != vt'))
}

--this guarantees a better reliability score for users logging in with the SPID authentication system
fact reliabilityScoreInit {
    all u, u' : User | (u!=u' and u.authentication.authenticationType = SPIDAuthentication
        and u'.authentication.authenticationType = ProprietaryAuthentication
        and #u.reportsMade = 0 and #u'.reportsMade = 0) implies (u.reliabilityScore > u'.reliabilityScore)
}

--this fact is used to check wheter a violation has an assigned value of verification which is false as default
fact verificationManagement{
    all v : Violation | v.verified = False iff v.verified != True
}

--this guarantees the possibility of an authority to increase a certain violation reporting user reliability score in case of
--his violation was verified by this authority
fact reliabilityScoreManagement {
    all u, u' : User | u = u' and (some x : Int | x > 0 and (u'.reliabilityScore = u.reliabilityScore + x)) iff
    (some v : Violation | v in u.reportsMade and v.verified = True)
}

--notification of violations
fact notificationFromUserToAuthority{
    all u: User | #u.reportsMade>0 iff (some a : Authority | let r = u.reportsMade | r in a.notification)
}

--user accessing service to create new violations
fact violationNotifier{
    all u : User | some v : Violation | v.email = u.email implies v in u.reportsMade
}

--needed to guarantee the autonomous notification system based on authorities current positions
fact notifyWhomManagement{
    all u : User, a : Authority | let r = u.reportsMade | r in a.notification iff (r.position = a.city.position)
}

--this grants the possibility to check on various SafeStreets statistics
fact statisticsVisualization{
   all v : ViolationVisualizer | some u : User | v = ViolationVisualizerPro implies u = Authority
   all v : ViolationVisualizer | some u : User | v = ViolationVisualizerLimited implies u = NormalUser
   all v1, v2 : ViolationVisualizer | v1 = v2 iff v1.map = v2.map
}

fact statistics{
    all v : ViolationVisualizer | #v.violation>0 iff (some u : User | #u.reportsMade>0)
}

--this following facts are needed to guarantee a working suggestion inferring system
fact municipalityDataManagement{
    all s : SuggestionInferralEngine | #s.suggestions>0 implies (#s.municipalities>0 and (some v : Violation | #v>0))
    all s : SuggestionInferralEngine | all m : Municipality | m in s.municipalities and #m.incidents>0
       and (all m' : Municipality  | ( m.city = m'.city or m.incidents = m'.incidents) iff m = m')
    all m1, m2 : Municipality | m1.city = m2.city implies m1 = m2
}

fact suggestionsActivation{
    all s : SuggestionInferralEngine, v : Violation | #s.suggestions>0 implies (#s.municipalities>0 and #v>0)
}

fact municipalityDataProvided{
    all s : SuggestionInferralEngine | (#s.municipalities>0 and (some u : User | #u.reportsMade>0)) 
    implies (some a : Authority | s.suggestions in a.suggestions)
}

--world regarding SafeStreets accesed by registred authorities and users
pred Registration {
    #NormalUser = 1
    #Authority = 1
}

run Registration for 3 but 0 SuggestionsType, 0 MunicipalityData

--world regarding the visualization of the violations map with the different levels of visibility depedning on the user type
pred VisualizerMap {
    #ViolationVisualizerLimited = 1
    #ViolationVisualizerPro = 1
}

run VisualizerMap for 2 but 0 SuggestionsType, 0 MunicipalityData

--world regarding the new suggestions inferred by SafeStreets by using municipality data
pred Suggestions{
    #SuggestionInferralEngine = 1
    #Municipality = 2
}
run Suggestions for 3

--really important assert to guarantee authority access to his various assigned special SafeStreets functionalities
assert AuthorityRecognition {
    no a : Authority | no c : DigitalCertificateX509 | a.authorization.id = c.id
}
check AuthorityRecognition

--The presented Alloy code was made to be as clear as possible considering the respective UML which will be more detailed for obvious reasons