<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::table('broker', function (Blueprint $table) {
            $table->enum ('is_email', ['Y', 'N'])->default('N');
            $table->enum ('is_sms', ['Y', 'N'])->default('N');
            $table->enum ('default_otp', ['Y', 'N'])->default('N');
            $table->integer('master_otp')->nullable();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('broker', function (Blueprint $table) {
            $table->dropColumn('is_email');
            $table->dropColumn('is_sms');
            $table->dropColumn('default_otp');
            $table->dropColumn('master_otp');
        });
    }
};
