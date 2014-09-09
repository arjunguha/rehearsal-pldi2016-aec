using System.ComponentModel.DataAnnotations;

namespace $rootnamespace$.Models
{
    public partial class EmailModel
    {
        [DataType(DataType.EmailAddress)]
        [Required]
        public string EmailAddress { get; set; }

        public bool IsDefault { get; set; }
    }
}