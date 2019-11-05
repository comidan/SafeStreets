abstract sig Quality{}
sig MODIFIED extends Quality{}
sig NONMODIFIED extends Quality{}

sig Username{}

sig Password{}

sig Name{}

sig Surname{}

sig AuthenticatorID{}

sig FiscalCode{}

sig City{}

sig Address{}

sig PhoneNumber{}

sig ID{}

sig Email{}

sig CertifiedEmail extends Email{}

sig DigitalCertificateX509{
    creationDate : one TimeStamp,
    dateOfExpiry : one TimeStamp,
    id : one ID
} {creationDate.milliseconds < dateOfExpiry.milliseconds}

sig ViolationType{}

sig LicensePlate{}

sig Position{}

sig Note{
    length : one Int
}

sig Image {
    status : one Int
}

sig Date{ 
    day : one Int,
    month : one Int,
    year : one Int
}

sig TimeStamp extends Date {
    milliseconds : Int
}

sig Authorization {
    digitalCertificateX509 : one DigitalCertificateX509
}

abstract sig AuthentiaticationType {}
sig SPIDAuthentication extends AuthentiaticationType {}
sig ProprietaryAuthentication extends AuthentiaticationType {}

sig Authentication {
    authenticationType : one AuthentiaticationType,
    username : one Username,
    password : one Password
}

abstract sig User {
    name : one Name,
    surname : one Surname,
    autheticatorID : one AuthenticatorID,
    authentication : one Authentication,
    reportsMade : some Violation
}

sig NormalUser extends User {
    reliabilityScore : one Int,
    birthDate : one Date,
    fiscalCode : one FiscalCode,
    birthLocation : one City,
    phoneNumber : one PhoneNumber,
    city : one City,
    address : one Address,
    email: one Email
}

sig Authority extends User {
    authorization : one Authorization,
    certifiedEmail : one CertifiedEmail
}

sig Violation {
    violationType : some ViolationType,
    image : one Image,
    licensePlate : one LicensePlate,
    quality : one Quality,
    position : one Position,
    timeStamp : one TimeStamp,
    note : one Note,
    email : one Email,
    autheticatorID : one AuthenticatorID,
    verified : one Int
} {note.length <= 140 && note.length > 0}

sig ViolationControl {
    reports : some Violation
}

sig Map{}

sig ViolationVisualizer {
    map : one Map
}

abstract sig ViolationLimited {
    violationType : some ViolationType,
    position : one Position,
    timeStamp : one TimeStamp
}

sig ViolationVisualizerLimited extends ViolationVisualizer {
    violationLimited : some ViolationLimited
}

sig ViolationVisualizerPro extends ViolationVisualizer {
    violations : some Violation
}

sig Data{}

sig MunicipalityData {
    data : some Data
} {#data >= 1}

sig SuggestionInferred {
    municipalityData : one MunicipalityData
}

sig SuggestionInferralEngine {
    suggestions : some SuggestionInferred
}

fact violationTypeLimit {
	no v: Violation | #v.violationType > 3
}

fact noDuplicateUser {
    no u1, u2 : User | u1.autheticatorID = u2.autheticatorID
}

fact noDuplicatePerson {
    all u1, u2 : NormalUser | u1.autheticatorID != u2.autheticatorID
    implies u1.fiscalCode != u2.fiscalCode and u1.email != u2.email
}

fact noDuplicateAuthority {
    all a1, a2 : Authority | a1.autheticatorID != a2.autheticatorID
    implies a1.certifiedEmail != a2.certifiedEmail
}

fact noDuplicateDigitalCertificateX509 {
    no c1, c2 : DigitalCertificateX509 | c1.id = c2.id
}

fact noDuplicateViolationsFromAnUser {
    all v1, v2 : Violation | v1.autheticatorID = v2.autheticatorID
    implies {
        v1.licensePlate != v2.licensePlate => v1.timeStamp.milliseconds - v2.timeStamp.milliseconds < 1200000 
        and v1.position != v2.position
    }
}

fact noDuplicateViolationTypes {
    all vt, vt', vt'' : ViolationType, v: Violation | 
        ((#v.violationType=3 and vt in v.violationType and vt' in v.violationType and vt'' in v.violationType) 
            => (vt != vt' and vt' != vt'' and vt != vt'')) or
        ((#v.violationType=2 and vt in v.violationType and vt' in v.violationType) => (vt != vt'))
}