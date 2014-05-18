using System;
using System.ComponentModel.DataAnnotations;
using System.Runtime.Serialization;

namespace $rootnamespace$.Models
{
    public partial class ProfileModel
    {
        [Required]
        [Display(Name = "First Name")]
        public string FirstName { get; set; }

        [Required]
        [Display(Name = "Last name")]
        public string LastName { get; set; }

        [Required]
        [DataType(DataType.EmailAddress)]
        public virtual String Email { get; set; }
    }
}