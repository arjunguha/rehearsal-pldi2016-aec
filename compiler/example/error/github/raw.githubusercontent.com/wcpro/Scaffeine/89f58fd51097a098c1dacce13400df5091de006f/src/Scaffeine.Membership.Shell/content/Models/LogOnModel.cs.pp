namespace $rootnamespace$.Models
{
    using System.ComponentModel.DataAnnotations;
    using Attributes;

    public partial class LogOnModel
    {
        [Required]
        [Display(Name = "Username")]
        [Textbox(TextboxSize = TextboxSize.Medium)]
        public string UserName { get; set; }

        [Required]
        [DataType(DataType.Password)]
        [Display(Name = "Password")]
        [Password(TextboxSize = TextboxSize.Medium)]
        public string Password { get; set; }
        
        [Display(Name = "Remember me?")]
        public bool RememberMe { get; set; }
    }
}