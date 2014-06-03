namespace $rootnamespace$.Models
{
    using System;
    using System.ComponentModel.DataAnnotations;
    using Attributes;

    public class CreditCardModel
    {
        public CreditCardModel()
        {
            Month = DateTime.Now.Month.ToString("00");
            Year = DateTime.Now.Year.ToString();
        }

        [DataType(DataType.CreditCard)]
        [Required]
        [Display(Name = "Card Number")]
        [RegularExpression(@"^[0-9]+$", ErrorMessage = "Credit card numbers must only contain numbers")]
        [StringLength(16, MinimumLength = 12, ErrorMessage = "Credit card numbers must be between 12 and 16 characters long")]
        public string CreditCardNumber { get; set; }

        [Required]
        [Display(Name="Card Type")]
        [DropDown("CreditCardTypes")]
        [Textbox(TextboxSize = TextboxSize.Medium)]
        public string CardType { get; set; }

        [Required]
        [Display(Name="CVV Code")]
        [Range(100,9999, ErrorMessage = "Please enter a valid CVV code")]
        [Textbox(TextboxSize = TextboxSize.Mini)]
        public string CVV { get; set; }

        [Required]
        [Display(Name = "Exp. Month")]
        [DropDown("Months")]
        public string Month { get; set; }

        [Required]
        [Display(Name="Exp. Year")]
        [Textbox(TextboxSize = TextboxSize.Medium)]
        [DropDown("CreditCardExpirationYears")]
        public string Year { get; set; }        
    }
}