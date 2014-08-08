using System;
using System.ComponentModel.DataAnnotations;

namespace $rootnamespace$.Models
{
    public partial class ContactUsModel
    {
        [MinLength(5)]
        [Required]
        public string Name { get; set; }

        [DataType(DataType.EmailAddress)]
        [Required]
        public string Email { get; set; }

        [MinLength(5)]
        [DataType(DataType.MultilineText)]
        public string Message { get; set; }
    }
}